import Init.Data.Array
import Init.Data.Int
import Std.Data.RBMap
import Init.System.IO

import LeanLLVM.AST
import LeanLLVM.PP
import LeanLLVM.Parser
import LeanLLVM.DataLayout
import LeanLLVM.LLVMFFI

open Std (RBMap)

namespace Option

universes u v

def mapM {m:Type u → Type v} {α β:Type u} [Applicative m] (f:α → m β) : Option α → m (Option β)
| none => pure none
| some x => some <$> f x

end Option

-- Type for pointers
--
-- USize compiles to a size_t when unboxed.  Technically pointers
-- should map to intptr_t instead of size_t, but `size_t` is the
-- same size on x86_64.
structure Ptr :=
(val : USize)

namespace Ptr

protected def toString (x:Ptr) : String := "0x" ++ (Nat.toDigits 16 x.val.toNat).asString

instance : ToString Ptr := ⟨Ptr.toString⟩

end Ptr

namespace LLVM

@[reducible]
def aliasMap := RBMap String TypeDeclBody (λx y => decide (x < y))

@[reducible]
def visitMap := RBMap String Unit (λx y => decide (x < y))

def extract (a:Type) : Type := IO.Ref (aliasMap × visitMap) -> IO a

namespace extract

instance monad : Monad extract :=
  { bind := λmx mf r => mx r >>= λx => mf x r
  , pure := λx r => pure x
  }

instance monadExcept : MonadExcept IO.Error extract :=
  { throw := λerr r => throw err
  , tryCatch := λm handle r => tryCatch (m r) (λerr => handle err r)
  }

instance mIO : MonadLiftT IO extract := { monadLift := λ m r => m }

def run {a:Type} (m:extract a) : IO (aliasMap × a) := do
  let r <- IO.mkRef (Std.RBMap.empty, Std.RBMap.empty);
  let a <- m r;
  let (mp,_) <- r.get;
  pure (mp, a)

-- Execute this action when extracting a named structure
-- type.  This will track the set of already-visited aliases.
-- If the named type has previously been visited, this
-- action will return true.  If false, the type alias definition
-- still needs to be converted.  It is important to call 'visit'
-- on a named type before extracting its definition to break recursive
-- cycles in structure definitions.
def visit (nm:String) : extract Bool := λref => do
  let (am,vm) <- ref.get;
  match vm.find? nm with
  | some () => pure true
  | none => do
    let vm' := Std.RBMap.insert vm nm ();
    ref.set (am, vm');
    pure false

-- After visiting a named structure type, this action should be
-- called to register the body of the named alias.
def define (nm:String) (body:TypeDeclBody) : extract Unit := λref => do
  let (am,vm) <- ref.get;
  let am' := Std.RBMap.insert am nm body;
  ref.set (am',vm);
  pure ()

end extract

section

open Code

def typeIsVoid (tp : FFI.Type_) : IO Bool := do
  let id <- FFI.getTypeTag tp;
  match id with
  | TypeID.void => pure true
  | _ => pure false

def throwError {α} (msg:String): extract α := throw (IO.userError msg)

partial def extractType (tp : FFI.Type_) : extract LLVMType := do
  let id <- FFI.getTypeTag tp;
  match id with
  | TypeID.void      => pure $ PrimType.void
  | TypeID.half      => pure $ FloatType.half
  | TypeID.float     => pure $ FloatType.float
  | TypeID.double    => pure $ FloatType.double
  | TypeID.x86FP80   => pure $ FloatType.x86FP80
  | TypeID.fp128     => pure $ FloatType.fp128
  | TypeID.ppcFP128  => pure $ FloatType.ppcFP128
  | TypeID.label     => pure $ PrimType.label
  | TypeID.metadata  => pure $ PrimType.metadata
  | TypeID.x86mmx    => pure $ PrimType.x86mmx
  | TypeID.token     => pure $ PrimType.token
  | TypeID.integer   =>
    (λn => PrimType.integer n) <$> FFI.getIntegerTypeWidth tp
  | TypeID.function => do
    let dt <- (FFI.getFunctionTypeData tp);
    match dt with
    | some (ret, args, varargs) => do
       let ret' <- extractType ret;
       let args' <- Array.mapM extractType args;
       pure $ LLVMType.funType ret' args' varargs
    | none => throwError "expected function type!"
  | TypeID.struct => do
     let tn <- FFI.getTypeName tp;
     match tn with
     | some nm => do
       -- named struct type, check if we need to traverse the type definition
       -- only recurse into the definition if this is the first time
       -- we've encountered this named type
       unless (← extract.visit nm) do
         let opq <- FFI.typeIsOpaque tp;
         match opq with
         | true => extract.define nm TypeDeclBody.opaque
         | false => do
           let dt <- FFI.getStructTypeData tp;
           match dt with
           | some (packed, tps) => do
             let tps' <- Array.mapM extractType tps;
             extract.define nm (TypeDeclBody.defn (LLVMType.struct packed tps'))
           | none => throwError "expected struct type!";
       pure $ LLVMType.alias nm
     -- literal struct type, recurse into it's definition
     | none => do
       let dt <- FFI.getStructTypeData tp;
       match dt with
       | some (packed, tps)  => LLVMType.struct packed <$> Array.mapM extractType tps
       | none => throwError "expected struct type!"
  | TypeID.array => do
    let dt <- (FFI.getSequentialTypeData tp);
    match dt with
    | some (n, el) => LLVMType.array n <$> extractType el
    | none => throwError "expected array type!"
  | TypeID.pointer => do
    let eltp <- (FFI.getPointerElementType tp);
    match eltp with
    | none => throwError "expected pointer type!"
    | some x => LLVMType.ptr <$> extractType x
  | TypeID.vector => do
     let dt <- (FFI.getSequentialTypeData tp);
     match dt with
     | some (n, el) => LLVMType.vector n <$> extractType el
     | none => throwError "expected vector type!"

end

def InstrMap := RBMap FFI.Instruction Ident FFI.instructionLt

def BBMap := RBMap FFI.BasicBlock BlockLabel FFI.basicBlockLt

def BBMap.empty : BBMap := Std.RBMap.empty

structure ValueContext :=
  (funArgs : Array (Typed Ident))
  (imap : InstrMap)
  (bmap : BBMap)

def ValueContext.empty : ValueContext :=
  { funArgs := Array.empty,
    imap := Std.RBMap.empty,
    bmap :=  Std.RBMap.empty
  }

def extractArgs (fn : FFI.Function) : extract (Nat × Array (Typed Ident)) := do
  let rawargs ← (FFI.getFunctionArgs fn)
  let mut counter : Nat := 0
  let mut args : Array (Typed Ident) := Array.empty
  for (mnm, rawtp) in rawargs do
    let tp ← extractType rawtp
    match mnm with
    | none    => 
      counter := counter+1
      args := Array.push args ⟨tp, Ident.anon counter⟩
    | some nm => 
      counter := counter
      args    := Array.push args ⟨tp, Ident.named nm⟩
  pure (counter, args)

def extractBBLabel (bb:FFI.BasicBlock) (c:Nat) : extract (Nat × BlockLabel) := do
  let nm <- (FFI.getBBName bb);
  match nm with
  | none    => pure (c+1, ⟨Ident.anon c⟩)
  | some nm => pure (c  , ⟨Ident.named nm⟩)


def computeInstructionNumbering
  (rawbb:FFI.BasicBlock)
  (c0:Nat)
  (imap0:InstrMap)
  : extract (Nat × InstrMap) := do
  let instrarr <- (FFI.getInstructionArray rawbb);
  let mut c := c0
  let mut imap := imap0
  for rawi in instrarr do
    let tp ← (FFI.getInstructionType rawi)
    let isv ← (typeIsVoid tp)
    unless isv do
      let mnm ← (FFI.getInstructionName rawi)
      match mnm with
      | some nm => 
        imap := Std.RBMap.insert imap rawi (Ident.named nm)
      | none    =>
        c := c+1
        imap := Std.RBMap.insert imap rawi (Ident.anon c)
  pure (c, imap)


def computeNumberings (c0:Nat) (fn:FFI.Function) : extract (BBMap × InstrMap) := do
   let bbarr ← (FFI.getBasicBlockArray fn)
   let mut c := c0
   let mut bmap := BBMap.empty
   let mut imap : InstrMap := Std.RBMap.empty
   for rawbb in bbarr do
     let (c', blab) ← extractBBLabel rawbb c
     bmap := Std.RBMap.insert bmap rawbb blab
     (c, imap) <- computeInstructionNumbering rawbb c' imap;
   pure (bmap, imap)

partial def extractConstant (rawc : FFI.Constant) : extract Value := do
  let extractTypedConstant (c:FFI.Constant) : extract (Typed Value) := do
    let tp ← (FFI.getValueType c) >>= extractType
    let x  ← extractConstant c
    pure ⟨tp, x⟩
  let tag ← (FFI.getConstantTag rawc)
  match tag with
  | Code.Const.ConstantInt => do
    let d ← (FFI.getConstIntData rawc)
    match d with
    | some (_w, v) => pure (Value.integer (Int.ofNat v))
    | none => throwError "expected constant integer value"
  | Code.Const.Function => do
    let nm ← (FFI.getConstantName rawc)
    match nm with
    | some s => pure (Symbol.mk s)
    | none   => throwError "expected function value"
  | Code.Const.GlobalVariable => do
    let nm ← (FFI.getConstantName rawc)
    match nm with
    | some s => pure (Symbol.mk s)
    | none   => throwError "expected global variable"
  | Code.Const.ConstantPointerNull =>
    pure Value.null
  | Code.Const.ConstantDataArray => do
    let md ← FFI.getConstArrayData rawc
    match md with
    | none => throwError "expected constant array"
    | some (elty, cs) => do
      let elty' ← extractType elty
      let cs' ← cs.mapM extractConstant
      pure (Value.array elty' cs')
  | Code.Const.ConstantExpr => do
    let md ← (FFI.getConstExprData rawc)
    match md with
    | none => throwError "expected constant expression"
    | some (op, xs) =>
      match op with
      | Code.Instr.GetElementPtr => do
        let cs ← Array.mapM extractTypedConstant xs
        pure $ ConstExpr.gep false none PrimType.void cs
      | _ =>
        throwError $ "unexpected (or unimplemented) constant instruction opcode: " ++ op.asString
   | Code.Const.UndefValue => pure Value.undef
   | _ => throwError $ "unknown constant value: " ++ tag.asString

def extractValue (ctx:ValueContext) (rawv:FFI.Value) : extract Value := do
  let decmp ← FFI.decomposeValue rawv
  match decmp with
  | FFI.ValueView.constantView c => extractConstant c
  | FFI.ValueView.argument n =>
    match Array.get? ctx.funArgs n with
    | none => throwError "invalid argument value"
    | some i => pure (Value.ident i.value)
  | FFI.ValueView.instruction i =>
    match Std.RBMap.find? ctx.imap i with
    | none   => throwError "invalid instruction value"
    | some i => pure (Value.ident i)
  | FFI.ValueView.block b =>
    throwError "unimplemented: basic block value"
  | FFI.ValueView.inlineasm i => do
    let (hasSideEffects, (isAlignStack, (asmString, constraintString))) ←
      (FFI.getInlineAsmData i)
    pure (Value.asm hasSideEffects isAlignStack asmString constraintString)
  
  | FFI.ValueView.unknown => throwError "unknown value"

def extractBlockLabel (ctx:ValueContext) (bb:FFI.BasicBlock) : extract BlockLabel :=
  match Std.RBMap.find? ctx.bmap bb with
  | none => throwError "unknown basic block"
  | some lab => pure lab

def extractTypedValue (ctx:ValueContext) (rawv:FFI.Value) : extract (Typed Value) := do
   let tp ← (FFI.getValueType rawv) >>= extractType;
   let v  ← extractValue ctx rawv;
   pure ⟨tp, v⟩

def extractBinaryOp (rawInstr:FFI.Instruction)
                    (ctx:ValueContext)
                    (f:Typed Value → Value → Instruction) : extract Instruction := do
  let x ← (FFI.getBinaryOperatorValues rawInstr)
  match x with
  | none => throwError "expected binary operation"
  | some (o1,o2) => do
    let v1 ← extractTypedValue ctx o1
    let v2 ← extractTypedValue ctx o2
    pure (f v1 v2.value)

def extractCastOp (rawinstr:FFI.Instruction)
                  (ctx:ValueContext)
                  (f:Typed Value → LLVMType → Instruction) : extract Instruction := do
  let x ← FFI.getCastInstData rawinstr
  match x with
  | none => throwError "expected conversion instruction"
  | some (_op, v) => do
    let tv ← extractTypedValue ctx v
    let outty ← (FFI.getInstructionType rawinstr) >>= extractType
    pure (f tv outty)

def extractICmpOp (n:Code.ICmp) : ICmpOp :=
  match n with
  | Code.ICmp.eq  => ICmpOp.ieq
  | Code.ICmp.ne  => ICmpOp.ine
  | Code.ICmp.ugt => ICmpOp.iugt
  | Code.ICmp.uge => ICmpOp.iuge
  | Code.ICmp.ult => ICmpOp.iult
  | Code.ICmp.ule => ICmpOp.iule
  | Code.ICmp.sgt => ICmpOp.isgt
  | Code.ICmp.sge => ICmpOp.isge
  | Code.ICmp.slt => ICmpOp.islt
  | Code.ICmp.sle => ICmpOp.isle

def extractInstruction (rawinstr:FFI.Instruction) (ctx:ValueContext) : extract Instruction := do
  let op ← (FFI.getInstructionOpcode rawinstr)
  let tp ← (FFI.getInstructionType rawinstr) >>= extractType
  match op with
  -- == terminators ==
  -- return
  | Code.Instr.Ret => do
    let mv ← FFI.getInstructionReturnValue rawinstr
    match mv with
    | none => pure Instruction.retVoid
    | some v => Instruction.ret <$> extractTypedValue ctx v
  -- br
  | Code.Instr.Br => do
    let d ← FFI.getBranchInstData rawinstr
    match d with
    | none => throwError "expected branch instruction"
    | some (FFI.BranchView.unconditional b) =>
      Instruction.jump <$> extractBlockLabel ctx b
    | some (FFI.BranchView.conditional c t f) => do
      let cv ← extractTypedValue ctx c
      let tl ← extractBlockLabel ctx t
      let fl ← extractBlockLabel ctx f
      pure (Instruction.br cv tl fl)

     -- unreachable
  | Code.Instr.Unreachable => pure Instruction.unreachable

    -- == binary operators ==
    -- add
  | Code.Instr.Add => do
    let uov ← (FFI.hasNoUnsignedWrap rawinstr)
    let sov ← (FFI.hasNoSignedWrap rawinstr)
    extractBinaryOp rawinstr ctx (Instruction.arith (ArithOp.add uov sov))
    -- fadd
  | Code.Instr.FAdd =>
    extractBinaryOp rawinstr ctx (Instruction.arith ArithOp.fadd)
    -- sub
  | Code.Instr.Sub => do
    let uov ← (FFI.hasNoUnsignedWrap rawinstr)
    let sov ← (FFI.hasNoSignedWrap rawinstr)
    extractBinaryOp rawinstr ctx (Instruction.arith (ArithOp.sub uov sov))
  -- fsub
  | Code.Instr.FSub =>
    extractBinaryOp rawinstr ctx (Instruction.arith ArithOp.fsub)
  -- mul
  | Code.Instr.Mul => do
    let uov ← (FFI.hasNoUnsignedWrap rawinstr)
    let sov ← (FFI.hasNoSignedWrap rawinstr)
    extractBinaryOp rawinstr ctx (Instruction.arith (ArithOp.mul uov sov))
  -- fmul
  | Code.Instr.FMul => extractBinaryOp rawinstr ctx (Instruction.arith ArithOp.fmul)
  -- udiv
  | Code.Instr.UDiv => do
    let ex ← (FFI.isExact rawinstr);
    extractBinaryOp rawinstr ctx (Instruction.arith (ArithOp.udiv ex))
  -- sdiv
  | Code.Instr.SDiv => do
    let ex ← (FFI.isExact rawinstr);
    extractBinaryOp rawinstr ctx (Instruction.arith (ArithOp.sdiv ex))
  -- fdiv
  | Code.Instr.FDiv =>
    extractBinaryOp rawinstr ctx (Instruction.arith ArithOp.fdiv)
  -- urem
  | Code.Instr.URem =>
    extractBinaryOp rawinstr ctx (Instruction.arith ArithOp.urem)
  -- srem
  | Code.Instr.SRem =>
    extractBinaryOp rawinstr ctx (Instruction.arith ArithOp.srem)
  -- frem
  | Code.Instr.FRem =>
    extractBinaryOp rawinstr ctx (Instruction.arith ArithOp.frem)
  -- shl
  | Code.Instr.Shl => do
    let uov ← (FFI.hasNoUnsignedWrap rawinstr)
    let sov ← (FFI.hasNoSignedWrap rawinstr)
    extractBinaryOp rawinstr ctx (Instruction.bit (BitOp.shl uov sov))
  -- lshr
  | Code.Instr.LShr => do
    let ex ← (FFI.isExact rawinstr);
    extractBinaryOp rawinstr ctx (Instruction.bit (BitOp.lshr ex))
  -- ashr
  | Code.Instr.AShr => do
    let ex ← (FFI.isExact rawinstr)
    extractBinaryOp rawinstr ctx (Instruction.bit (BitOp.ashr ex))
  -- and
  | Code.Instr.And => extractBinaryOp rawinstr ctx (Instruction.bit BitOp.and)
  -- or
  | Code.Instr.Or => extractBinaryOp rawinstr ctx (Instruction.bit BitOp.or)
  -- xor
  | Code.Instr.Xor => extractBinaryOp rawinstr ctx (Instruction.bit BitOp.xor)
  -- alloca
  | Code.Instr.Alloca => do
     let md ← (FFI.getAllocaData rawinstr)
     match md with
     | none => throwError "Expected alloca instruction"
     | some (tp, nelts, align) => do
       let tp' <- extractType tp
       let nelts' <- Option.mapM (extractTypedValue ctx) nelts
       pure (Instruction.alloca tp' nelts' align)
  -- load
  | Code.Instr.Load => do
    let md ← (FFI.getLoadData rawinstr)
    match md with
    | none => throwError "Expected load instruction"
    | some (ptr, align) => do
      let ptr' ← extractTypedValue ctx ptr
      pure (Instruction.load ptr' none align) -- TODO atomic ordering
  -- store
  | Code.Instr.Store => do
    let md ← (FFI.getStoreData rawinstr)
    match md with
    | none => throwError "Expected store instruction"
    | some (val,ptr,align) => do
      let val' ← extractTypedValue ctx val
      let ptr' ← extractTypedValue ctx ptr
      pure (Instruction.store val' ptr' align)
  -- GEP
   | Code.Instr.GetElementPtr => do
     let md ← (FFI.getGEPData rawinstr)
     match md with
     | none => throwError "Expected GEP instruction"
     | some (inbounds,base,idxes) => do
       let base' ← extractTypedValue ctx base
       let idxes' ← Array.mapM (extractTypedValue ctx) idxes
       pure (Instruction.gep inbounds base' idxes')
   -- trunc
   | Code.Instr.Trunc => extractCastOp rawinstr ctx (Instruction.conv ConvOp.trunc)
   -- zext
   | Code.Instr.ZExt => extractCastOp rawinstr ctx (Instruction.conv ConvOp.zext)
   -- sext
   | Code.Instr.SExt => extractCastOp rawinstr ctx (Instruction.conv ConvOp.sext)
   -- fptoui
   | Code.Instr.FPToUI => extractCastOp rawinstr ctx (Instruction.conv ConvOp.fp_to_ui)
   -- fptosi
   | Code.Instr.FPToSI => extractCastOp rawinstr ctx (Instruction.conv ConvOp.fp_to_si)
   -- uitofp
   | Code.Instr.UIToFP => extractCastOp rawinstr ctx (Instruction.conv ConvOp.ui_to_fp)
   -- sitofp
   | Code.Instr.SIToFP => extractCastOp rawinstr ctx (Instruction.conv ConvOp.si_to_fp)
   -- fptrunc
   | Code.Instr.FPTrunc => extractCastOp rawinstr ctx (Instruction.conv ConvOp.fp_trunc)
   -- fpext
   | Code.Instr.FPExt => extractCastOp rawinstr ctx (Instruction.conv ConvOp.fp_ext)
   -- ptrtoint
   | Code.Instr.PtrToInt => extractCastOp rawinstr ctx (Instruction.conv ConvOp.ptr_to_int)
   -- inttoptr
   | Code.Instr.IntToPtr => extractCastOp rawinstr ctx (Instruction.conv ConvOp.int_to_ptr)
   -- bitcast
   | Code.Instr.BitCast => extractCastOp rawinstr ctx (Instruction.conv ConvOp.bit_cast)
   -- icmp
   | Code.Instr.ICmp => do
     let d ← (FFI.getICmpInstData rawinstr)
     match d with
     | none => throwError "expected icmp instruction"
     | some (code, (v1, v2)) => do
       let op := extractICmpOp code
       let o1 ← extractTypedValue ctx v1
       let o2 ← extractTypedValue ctx v2
       pure (Instruction.icmp op o1 o2.value)

   -- PHI
   | Code.Instr.PHI => do
     let t ← (FFI.getInstructionType rawinstr) >>= extractType
     let d ← (FFI.getPhiData rawinstr)
     match d with
     | none => throwError "expected phi instruction"
     | some vs => do
       let vs' <- vs.mapM $ λ vbb =>
         Prod.mk <$> extractValue ctx vbb.1 <*> extractBlockLabel ctx vbb.2
       pure (Instruction.phi t vs')
   -- call
   | Code.Instr.Call => do
     let d ← (FFI.getCallInstData rawinstr)
     match d with
     | none => throwError "expected call instruction"
     | some (tail,retty,funv,args) => do
       let retty' ← extractType retty
       let retty'' := match retty' with
                      | LLVMType.prim PrimType.void => none
                      | _ => some retty'
       let funv' ← extractTypedValue ctx funv
       let args' ← Array.mapM (extractTypedValue ctx) args;
       pure (Instruction.call tail retty'' funv'.value args')

   -- select
   | Code.Instr.Select => do
     let d ← (FFI.getSelectInstData rawinstr)
     match d with
     | none => throwError "expected select instruction"
     | some (vc, (vt,ve)) => do
       let c ← extractTypedValue ctx vc
       let t ← extractTypedValue ctx vt
       let e ← extractTypedValue ctx ve
       pure (Instruction.select c t e.value)

   -- extractvalue 
   | Code.Instr.ExtractValue => do
     let d ← (FFI.getExtractValueInstData rawinstr)
     match d with
     | none => throwError "expected extractvalue instruction"
     | some (vag, idxs) => do
       let ag ← extractTypedValue ctx vag
       pure (Instruction.extractvalue ag idxs)

   -- insertvalue
   | Code.Instr.InsertValue => do
     let d <- (FFI.getInsertValueInstData rawinstr)
     match d with
     | none => throwError "expected extractvalue instruction"
     | some (vag, (vel, idxs)) => do
       let ag ← extractTypedValue ctx vag
       let el ← extractTypedValue ctx vel
       pure (Instruction.insertvalue ag el idxs)

   | _ => throwError $ "unimplemented instruction opcode: " ++ op.asString

def extractStmt (rawinstr:FFI.Instruction) (ctx:ValueContext) : extract Stmt := do
  let i ← extractInstruction rawinstr ctx
  pure { assign := Std.RBMap.find? ctx.imap rawinstr,
         instr := i,
         metadata := Array.empty,
       }

def extractStatements (bb:FFI.BasicBlock) (ctx:ValueContext) : extract (Array Stmt) := do
  let rawinstrs ← (FFI.getInstructionArray bb)
  let mut stmts := Array.empty
  for rawinstr in rawinstrs do
    let stmt <- extractStmt rawinstr ctx
    stmts := Array.push stmts stmt
  pure stmts

def extractBasicBlocks (fn : FFI.Function) (ctx:ValueContext) : extract (Array BasicBlock) := do
  let rawbbs <- (FFI.getBasicBlockArray fn)
  let mut bs : Array BasicBlock := Array.empty
  for rawbb in rawbbs do
    match Std.RBMap.find? ctx.bmap rawbb with
    | none => throwError "unknown basic block"
    | some lab => do
      let stmts <- extractStatements rawbb ctx
      bs := Array.push bs { label := lab, stmts := stmts }
  pure bs

def extractFunction (fn : FFI.Function) : extract Define := do
  let nm ← (FFI.getFunctionName fn)
  let ret ← (FFI.getReturnType fn) >>= extractType
  let (counter, args) ← extractArgs fn
  let (bmap, imap) ← computeNumberings counter fn
  let ctx : ValueContext := { funArgs := args, imap := imap, bmap := bmap }
  let bbs <- extractBasicBlocks fn ctx
  pure { linkage := none,
         retType := ret,
         name    := ⟨nm⟩,
         args    := args,
         varArgs := false,
         attrs   := Array.empty,
         sec     := none,
         gc      := none,
         body    := bbs,
         metadata := Strmap.empty,
         comdat   := none,
       }

def extractDataLayout (m:FFI.Module) : extract (List LayoutSpec) := do
  let dlstr ← FFI.getModuleDataLayoutStr m
  match parse.run parse.data_layout dlstr with
  | Sum.inl (stk, str') =>
    throwError $ "Could not parse data layout string: " ++ dlstr ++ "  " ++ reprStr stk ++ "  " ++ str'
  | Sum.inr dl => pure dl

def extractGlobal (g:FFI.GlobalVar) : extract Global := do
  let tp ← (FFI.getValueType g) >>= extractType
  match tp with
  | LLVMType.ptr valtp => do
    let md ← (FFI.getGlobalVarData g)
    match md with
    | none => throwError "Expected global variable"
    | some (nm, val, align) => do
      let val' ← val.mapM (extractValue ValueContext.empty)
      let attrs : GlobalAttrs := {  linkage := none, visibility := none, const := false }
      pure { sym := ⟨nm⟩
           , attrs := attrs
           , type := valtp
           , value := val'
           , align := align
           , metadata := Strmap.empty
           }
  | _ => throwError ("Expected pointer type for global but got: " ++ (pp tp).render)

def extractModule (m:FFI.Module) : extract Module := do
  let nm ← (FFI.getModuleIdentifier m)
  let dl ← extractDataLayout m
  let fns ← (FFI.getFunctionArray m) >>= Array.mapM extractFunction
  let gs  ← (FFI.getGlobalArray m) >>= Array.mapM extractGlobal
  pure { sourceName := some nm
       , dataLayout := dl
       , types      := Array.empty  -- TODO
       , namedMD    := Array.empty  -- TODO
       , unnamedMD  := Array.empty  -- TODO
       , comdat     := Strmap.empty -- TODO
       , globals    := gs
       , declares   := Array.empty  -- TODO
       , defines    := fns
       , inlineAsm  := Array.empty  -- TODO
       , aliases    := Array.empty  -- TODO
       }

def toTypeDecl (x:String × TypeDeclBody) : TypeDecl := ⟨x.1, x.2⟩

def loadModule (m:FFI.Module) : IO Module := do
  let (am, mod) ← (extractModule m).run
  let tds := List.map toTypeDecl (am.toList)
  pure { mod with types := tds.toArray }

end LLVM
