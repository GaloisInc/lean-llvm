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

instance : HasToString Ptr := ⟨Ptr.toString⟩

end Ptr

namespace LLVM

@[reducible]
def aliasMap := RBMap String TypeDeclBody (λx y => decide (x < y)).

@[reducible]
def visitMap := RBMap String Unit (λx y => decide (x < y)).

@[reducible]
def extract (a:Type) : Type := IO.Ref (aliasMap × visitMap) -> IO a.

namespace extract

instance monad : Monad extract :=
  { bind := λa b mx mf r => mx r >>= λx => mf x r
  , pure := λa x r => pure x
  }

instance monadExcept : MonadExcept IO.Error extract :=
  { throw := λa err r => throw err
  , catch := λa m handle r => catch (m r) (λerr => handle err r)
  }

instance mIO : MonadIO extract := { monadLift := λa m r => m }

def run {a:Type} (m:extract a) : IO (aliasMap × a) := do
  r <- IO.mkRef (Std.RBMap.empty, Std.RBMap.empty);
  a <- m r;
  (mp,_) <- r.get;
  pure (mp, a)

-- Execute this action when extracting a named structure
-- type.  This will track the set of already-visited aliases.
-- If the named type has previously been visited, this
-- action will return true.  If false, the type alias definition
-- still needs to be converted.  It is important to call 'visit'
-- on a named type before extracting its definition to break recursive
-- cycles in structure definitions.
def visit (nm:String) : extract Bool := λref => do
  (am,vm) <- ref.get;
  match vm.find? nm with
  | some () => pure true
  | none => do
    let vm' := Std.RBMap.insert vm nm ();
    ref.set (am, vm');
    pure false

-- After visiting a named structure type, this action should be
-- called to register the body of the named alias.
def define (nm:String) (body:TypeDeclBody) : extract Unit := λref => do
  (am,vm) <- ref.get;
  let am' := Std.RBMap.insert am nm body;
  ref.set (am',vm);
  pure ()

end extract

section

open Code

def typeIsVoid (tp : FFI.Type_) : IO Bool := do
  id <- FFI.getTypeTag tp;
  match id with
  | TypeID.void => pure true
  | _ => pure false

def throwError {α} (msg:String): extract α := throw (IO.userError msg)

partial def extractType : FFI.Type_ → extract LLVMType | tp => do
  id <- monadLift $ FFI.getTypeTag tp;
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
    monadLift $ (λn => PrimType.integer n) <$> FFI.getIntegerTypeWidth tp
  | TypeID.function => do
    dt <- monadLift (FFI.getFunctionTypeData tp);
    match dt with
    | some (ret, args, varargs) => do
       ret' <- extractType ret;
       args' <- Array.mapM extractType args;
       pure $ LLVMType.funType ret' args' varargs
    | none => throwError "expected function type!"
  | TypeID.struct => do
     tn <- monadLift $ FFI.getTypeName tp;
     match tn with
     -- named struct type, check if we need to traverse the type definition
     | some nm => do
       alreadyVisited <- extract.visit nm;
       -- only recurse into the definition if this is the first time
       -- we've encountered this named type
       unless alreadyVisited $ (do
         opq <- monadLift $ FFI.typeIsOpaque tp;
         match opq with
         | true => extract.define nm TypeDeclBody.opaque
         | false => do
           dt <- monadLift $ FFI.getStructTypeData tp;
           match dt with
           | some (packed, tps) => do
             tps' <- Array.mapM extractType tps;
             extract.define nm (TypeDeclBody.defn (LLVMType.struct packed tps'))
           | none => throwError "expected struct type!");
       pure $ LLVMType.alias nm
     -- literal struct type, recurse into it's definition
     | none => do
       dt <- monadLift $ FFI.getStructTypeData tp;
       match dt with
       | some (packed, tps)  => LLVMType.struct packed <$> Array.mapM extractType tps
       | none => throwError "expected struct type!"
  | TypeID.array => do
    dt <- monadLift (FFI.getSequentialTypeData tp);
    match dt with
    | some (n, el) => LLVMType.array n <$> extractType el
    | none => throwError "expected array type!"
  | TypeID.pointer => do
    eltp <- monadLift (FFI.getPointerElementType tp);
    match eltp with
    | none => throwError "expected pointer type!"
    | some x => LLVMType.ptr <$> extractType x
  | TypeID.vector => do
     dt <- monadLift (FFI.getSequentialTypeData tp);
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
    bmap :=  Std.RBMap.empty,
  }

def extractArgs (fn : FFI.Function) : extract (Nat × Array (Typed Ident)) := do
  rawargs <- monadLift (FFI.getFunctionArgs fn);
  Array.iterateM rawargs (0, Array.empty) $ λ _ a b => do
    let (mnm, rawtp) := a;
    let (counter, args) := b;
    tp <- extractType rawtp;
    match mnm with
    | none    => pure (counter+1, Array.push args ⟨tp, Ident.anon counter⟩)
    | some nm => pure (counter,   Array.push args ⟨tp, Ident.named nm⟩)

def extractBBLabel (bb:FFI.BasicBlock) (c:Nat) : extract (Nat × BlockLabel) := do
  nm <- monadLift (FFI.getBBName bb);
  match nm with
  | none    => pure (c+1, ⟨Ident.anon c⟩)
  | some nm => pure (c  , ⟨Ident.named nm⟩)

def foo (b:Bool) : IO Nat := do
  when b $ (do
   IO.println "Hello";
   IO.println "World");
  pure 1

def computeInstructionNumbering (rawbb:FFI.BasicBlock) (c0:Nat) (imap0:InstrMap)
  : extract (Nat × InstrMap) := do
   instrarr <- monadLift (FFI.getInstructionArray rawbb);
   Array.iterateM instrarr (c0, imap0) $ λ _ rawi st => do
      let (c,imap) := st;
      tp <- monadLift (FFI.getInstructionType rawi);
      isv <- monadLift (typeIsVoid tp);
      if isv then
        pure (c,imap)
      else do
        mnm <- monadLift (FFI.getInstructionName rawi);
        match mnm with
        | some nm => pure (c,   Std.RBMap.insert imap rawi (Ident.named nm))
        | none    => pure (c+1, Std.RBMap.insert imap rawi (Ident.anon c))

def computeNumberings (c0:Nat) (fn:FFI.Function) : extract (BBMap × InstrMap) := do
   bbarr <- monadLift (FFI.getBasicBlockArray fn);
   (_,finalbmap, finalimap) <-
     Array.iterateM bbarr (c0, BBMap.empty, (Std.RBMap.empty : InstrMap)) $ (λ_ rawbb st => do
       let (c, bmap, imap) := st;
       (c', blab) <- extractBBLabel rawbb c;
       bmap' <- pure (Std.RBMap.insert bmap rawbb blab);
       (c'', imap') <- computeInstructionNumbering rawbb c' imap;
       pure (c'',bmap',imap'));
   pure (finalbmap, finalimap)

partial def extractConstant : FFI.Constant -> extract Value
| rawc => do
  let extractTypedConstant (c:FFI.Constant) : extract (Typed Value) := (do
        tp <- monadLift (FFI.getValueType c) >>= extractType;
        x  <- extractConstant c;
        pure ⟨tp, x⟩);
  tag <- monadLift (FFI.getConstantTag rawc);
  match tag with
  | Code.Const.ConstantInt => do
    d <- monadLift (FFI.getConstIntData rawc);
    match d with
    | some (_w, v) => pure (Value.integer (Int.ofNat v))
    | none => throwError "expected constant integer value"
  | Code.Const.Function => do
    nm <- monadLift (FFI.getConstantName rawc);
    match nm with
    | some s => pure (Symbol.mk s)
    | none   => throwError "expected function value"
  | Code.Const.GlobalVariable => do
    nm <- monadLift (FFI.getConstantName rawc);
    match nm with
    | some s => pure (Symbol.mk s)
    | none   => throwError "expected global variable"
  | Code.Const.ConstantPointerNull =>
    pure Value.null

  | Code.Const.ConstantDataArray => do
    md <- monadLift (FFI.getConstArrayData rawc);
    match md with
    | none => throwError "expected constant array"
    | some (elty, cs) => do
      elty' <- extractType elty;
      cs' <- cs.mapM extractConstant;
      pure (Value.array elty' cs')
  | Code.Const.ConstantExpr => do
    md <- monadLift (FFI.getConstExprData rawc);
    match md with
    | none => throwError "expected constant expression"
    | some (op, xs) =>
      match op with
      | Code.Instr.GetElementPtr => do
        cs <- Array.mapM extractTypedConstant xs;
        pure $ ConstExpr.gep false none PrimType.void cs
      | _ =>
        throwError $ "unexpected (or unimplemented) constant instruction opcode: " ++ op.asString
   | _ => throwError $ "unknown constant value: " ++ tag.asString

def extractValue (ctx:ValueContext) (rawv:FFI.Value) : extract Value := do
  decmp <- monadLift (FFI.decomposeValue rawv);
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
  | FFI.ValueView.unknown => throwError "unknown value"

def extractBlockLabel (ctx:ValueContext) (bb:FFI.BasicBlock) : extract BlockLabel :=
  match Std.RBMap.find? ctx.bmap bb with
  | none => throwError "unknown basic block"
  | some lab => pure lab

def extractTypedValue (ctx:ValueContext) (rawv:FFI.Value) : extract (Typed Value) := do
   tp <- monadLift (FFI.getValueType rawv) >>= extractType;
   v  <- extractValue ctx rawv;
   pure ⟨tp, v⟩

def extractBinaryOp (rawInstr:FFI.Instruction)
                    (ctx:ValueContext)
                    (f:Typed Value → Value → Instruction) : extract Instruction := do
  x <- monadLift (FFI.getBinaryOperatorValues rawInstr);
  match x with
  | none => throwError "expected binary operation"
  | some (o1,o2) => do
    v1 <- extractTypedValue ctx o1;
    v2 <- extractTypedValue ctx o2;
    pure (f v1 v2.value)

def extractCastOp (rawinstr:FFI.Instruction)
                  (ctx:ValueContext)
                  (f:Typed Value → LLVMType → Instruction) : extract Instruction := do
  x <- monadLift (FFI.getCastInstData rawinstr);
  match x with
  | none => throwError "expected conversion instruction"
  | some (_op, v) => do
    tv <- extractTypedValue ctx v;
    outty <- monadLift (FFI.getInstructionType rawinstr) >>= extractType;
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
  op <- monadLift (FFI.getInstructionOpcode rawinstr);
  tp <- monadLift (FFI.getInstructionType rawinstr) >>= extractType;
  match op with
  -- == terminators ==
  -- return
  | Code.Instr.Ret => do
    mv <- monadLift (FFI.getInstructionReturnValue rawinstr);
    match mv with
    | none => pure Instruction.retVoid
    | some v => Instruction.ret <$> extractTypedValue ctx v
  -- br
  | Code.Instr.Br => do
    d <- monadLift (FFI.getBranchInstData rawinstr);
    match d with
    | none => throwError "expected branch instruction"
    | some (FFI.BranchView.unconditional b) =>
      Instruction.jump <$> extractBlockLabel ctx b
    | some (FFI.BranchView.conditional c t f) => do
      cv <- extractTypedValue ctx c;
      tl <- extractBlockLabel ctx t;
      fl <- extractBlockLabel ctx f;
      pure (Instruction.br cv tl fl)

     -- unreachable
  | Code.Instr.Unreachable => pure Instruction.unreachable

    -- == binary operators ==
    -- add
  | Code.Instr.Add => do
    uov <- monadLift (FFI.hasNoUnsignedWrap rawinstr);
    sov <- monadLift (FFI.hasNoSignedWrap rawinstr);
    extractBinaryOp rawinstr ctx (Instruction.arith (ArithOp.add uov sov))
    -- fadd
  | Code.Instr.FAdd =>
    extractBinaryOp rawinstr ctx (Instruction.arith ArithOp.fadd)
    -- sub
  | Code.Instr.Sub => do
    uov <- monadLift (FFI.hasNoUnsignedWrap rawinstr);
    sov <- monadLift (FFI.hasNoSignedWrap rawinstr);
    extractBinaryOp rawinstr ctx (Instruction.arith (ArithOp.sub uov sov))
  -- fsub
  | Code.Instr.FSub =>
    extractBinaryOp rawinstr ctx (Instruction.arith ArithOp.fsub)
  -- mul
  | Code.Instr.Mul => do
    uov <- monadLift (FFI.hasNoUnsignedWrap rawinstr);
    sov <- monadLift (FFI.hasNoSignedWrap rawinstr);
    extractBinaryOp rawinstr ctx (Instruction.arith (ArithOp.mul uov sov))
  -- fmul
  | Code.Instr.FMul => extractBinaryOp rawinstr ctx (Instruction.arith ArithOp.fmul)
  -- udiv
  | Code.Instr.UDiv => do
    ex <- monadLift (FFI.isExact rawinstr);
    extractBinaryOp rawinstr ctx (Instruction.arith (ArithOp.udiv ex))
  -- sdiv
  | Code.Instr.SDiv => do
    ex <- monadLift (FFI.isExact rawinstr);
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
    uov <- monadLift (FFI.hasNoUnsignedWrap rawinstr);
    sov <- monadLift (FFI.hasNoSignedWrap rawinstr);
    extractBinaryOp rawinstr ctx (Instruction.bit (BitOp.shl uov sov))
  -- lshr
  | Code.Instr.LShr => do
    ex <- monadLift (FFI.isExact rawinstr);
    extractBinaryOp rawinstr ctx (Instruction.bit (BitOp.lshr ex))
  -- ashr
  | Code.Instr.AShr => do
    ex <- monadLift (FFI.isExact rawinstr);
    extractBinaryOp rawinstr ctx (Instruction.bit (BitOp.ashr ex))
  -- and
  | Code.Instr.And => extractBinaryOp rawinstr ctx (Instruction.bit BitOp.and)
  -- or
  | Code.Instr.Or => extractBinaryOp rawinstr ctx (Instruction.bit BitOp.or)
  -- xor
  | Code.Instr.Xor => extractBinaryOp rawinstr ctx (Instruction.bit BitOp.xor)
  -- alloca
  | Code.Instr.Alloca => do
     md ← monadLift (FFI.getAllocaData rawinstr);
     match md with
     | none => throwError "Expected alloca instruction"
     | some (tp, nelts, align) => do
       tp' <- extractType tp;
       nelts' <- Option.mapM (extractTypedValue ctx) nelts;
       pure (Instruction.alloca tp' nelts' align)
  -- load
  | Code.Instr.Load => do
    md ← monadLift (FFI.getLoadData rawinstr);
    match md with
    | none => throwError "Expected load instruction"
    | some (ptr, align) => do
      ptr' <- extractTypedValue ctx ptr;
      pure (Instruction.load ptr' none align) -- TODO atomic ordering
  -- store
  | Code.Instr.Store => do
    md ← monadLift (FFI.getStoreData rawinstr);
    match md with
    | none => throwError "Expected store instruction"
    | some (val,ptr,align) => do
      val' <- extractTypedValue ctx val;
      ptr' <- extractTypedValue ctx ptr;
      pure (Instruction.store val' ptr' align)
  -- GEP
   | Code.Instr.GetElementPtr => do
     md <- monadLift (FFI.getGEPData rawinstr);
     match md with
     | none => throwError "Expected GEP instruction"
     | some (inbounds,base,idxes) => do
       base' <- extractTypedValue ctx base;
       idxes' <- Array.mapM (extractTypedValue ctx) idxes;
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
     d <- monadLift (FFI.getICmpInstData rawinstr);
     match d with
     | none => throwError "expected icmp instruction"
     | some (code, (v1, v2)) => do
       let op := extractICmpOp code;
       o1 <- extractTypedValue ctx v1;
       o2 <- extractTypedValue ctx v2;
       pure (Instruction.icmp op o1 o2.value)

   -- PHI
   | Code.Instr.PHI => do
     t <- monadLift (FFI.getInstructionType rawinstr) >>= extractType;
     d <- monadLift (FFI.getPhiData rawinstr);
     match d with
     | none => throwError "expected phi instruction"
     | some vs => do
       vs' <- vs.mapM $ λvbb =>
         Prod.mk <$> extractValue ctx vbb.1 <*> extractBlockLabel ctx vbb.2;
       pure (Instruction.phi t vs')
   -- call
   | Code.Instr.Call => do
     d <- monadLift (FFI.getCallInstData rawinstr);
     match d with
     | none => throwError "expected call instruction"
     | some (tail,retty,funv,args) => do
       retty' <- extractType retty;
       let retty'' := match retty' with
                      | LLVMType.prim PrimType.void => none
                      | _ => some retty';
       funv'  <- extractTypedValue ctx funv;
       args'  <- Array.mapM (extractTypedValue ctx) args;
       pure (Instruction.call tail retty'' funv'.value args')

   -- select
   | Code.Instr.Select => do
     d <- monadLift (FFI.getSelectInstData rawinstr);
     match d with
     | none => throwError "expected select instruction"
     | some (vc, (vt,ve)) => do
       c <- extractTypedValue ctx vc;
       t <- extractTypedValue ctx vt;
       e <- extractTypedValue ctx ve;
       pure (Instruction.select c t e.value)

   | _ => throwError $ "unimplemented instruction opcode: " ++ op.asString

def extractStmt (rawinstr:FFI.Instruction) (ctx:ValueContext) : extract Stmt := do
  i <- extractInstruction rawinstr ctx;
  pure { assign := Std.RBMap.find? ctx.imap rawinstr,
         instr := i,
         metadata := Array.empty,
       }

def extractStatements (bb:FFI.BasicBlock) (ctx:ValueContext) : extract (Array Stmt) := do
  rawinstrs <- monadLift (FFI.getInstructionArray bb);
  Array.iterateM rawinstrs Array.empty (λ_ rawinstr stmts => do
    stmt <- extractStmt rawinstr ctx;
    pure (Array.push stmts stmt))

def extractBasicBlocks (fn : FFI.Function) (ctx:ValueContext) : extract (Array BasicBlock) := do
  rawbbs <- monadLift (FFI.getBasicBlockArray fn);
  Array.iterateM rawbbs Array.empty (λ_ rawbb bs =>
    match Std.RBMap.find? ctx.bmap rawbb with
    | none => throwError "unknown basic block"
    | some lab => do
      stmts <- extractStatements rawbb ctx;
      pure $ Array.push bs { label := lab, stmts := stmts })

def extractFunction (fn : FFI.Function) : extract Define := do
  nm <- monadLift (FFI.getFunctionName fn);
  ret <- monadLift (FFI.getReturnType fn) >>= extractType;
  (counter, args) <- extractArgs fn;
  (bmap, imap) <- computeNumberings counter fn;
  let ctx : ValueContext := { funArgs := args, imap := imap, bmap := bmap } ;
  bbs <- extractBasicBlocks fn ctx;
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
  dlstr <- monadLift $ FFI.getModuleDataLayoutStr m;
  match parse.run parse.data_layout dlstr with
  | Sum.inl (stk, str') =>
    throwError $ "Could not parse data layout string: " ++ dlstr ++ "  " ++ stk.repr ++ "  " ++ str'
  | Sum.inr dl => pure dl.

def extractGlobal (g:FFI.GlobalVar) : extract Global := do
  tp <- monadLift (FFI.getValueType g) >>= extractType;
  match tp with
  | LLVMType.ptr valtp => do
    md <- monadLift (FFI.getGlobalVarData g);
    match md with
    | none => throwError "Expected global variable"
    | some (nm, val, align) => do
      val' <- val.mapM (extractValue ValueContext.empty);
      let attrs : GlobalAttrs := {  linkage := none, visibility := none, const := false };
      pure { sym := ⟨nm⟩
           , attrs := attrs
           , type := valtp
           , value := val'
           , align := align
           , metadata := Strmap.empty
           }
  | _ => throwError ("Expected pointer type for global but got: " ++ (pp tp).render)

def extractModule (m:FFI.Module) : extract Module := do
  nm <- monadLift (FFI.getModuleIdentifier m);
  dl <- extractDataLayout m;
  fns <- monadLift (FFI.getFunctionArray m) >>= Array.mapM extractFunction;
  gs  <- monadLift (FFI.getGlobalArray m) >>= Array.mapM extractGlobal;
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
  (am, mod) <- (extractModule m).run;
  let tds := List.map toTypeDecl (am.toList);
  pure { mod with types := tds.toArray }

end LLVM
