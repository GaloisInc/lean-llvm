import Init.Data.Array
import Init.Data.Int
import Init.Data.RBMap
import Init.System.IO

import LeanLLVM.AST
import LeanLLVM.PP
import LeanLLVM.Parser
import LeanLLVM.DataLayout
import LeanLLVM.LLVMFFI

namespace Option
  universes u v.

  def mapM {m:Type u → Type v} {α β:Type u} [Applicative m] (f:α → m β) : Option α → m (Option β)
  | none => pure none
  | (some x) => some <$> f x
  .

end Option.

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

namespace llvm.

@[reducible]
def aliasMap := RBMap String type_decl_body (λx y => decide (x < y)).

@[reducible]
def visitMap := RBMap String Unit (λx y => decide (x < y)).

@[reducible]
def extract (a:Type) : Type := IO.Ref (aliasMap × visitMap) -> IO a.

namespace extract.

instance monad : Monad extract :=
  { bind := λa b mx mf r => mx r >>= λx => mf x r
  , pure := λa x r => pure x
  }.

instance monadExcept : MonadExcept IO.Error extract :=
  { throw := λa err r => throw err
  , catch := λa m handle r => catch (m r) (λerr => handle err r)
  }.

instance mIO : MonadIO extract :=
  { monadLift := λa m r => m
  }

def run {a:Type} (m:extract a) : IO (aliasMap × a) :=
  do r <- IO.mkRef (RBMap.empty, RBMap.empty);
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
def visit (nm:String) : extract Bool :=
  λref =>
    do (am,vm) <- ref.get;
       match vm.find nm with
       | some () => pure true
       | none =>
          do let vm' := RBMap.insert vm nm ();
             ref.set (am, vm');
             pure false

-- After visiting a named structure type, this action should be
-- called to register the body of the named alias.
def define (nm:String) (body:type_decl_body) : extract Unit :=
  λref =>
    do (am,vm) <- ref.get;
       let am' := RBMap.insert am nm body;
       ref.set (am',vm);
       pure ()

end extract.


def typeIsVoid (tp : ffi.Type_) : IO Bool :=
  do id <- ffi.getTypeTag tp;
     match id with
     | code.type.void => pure true
     | _ => pure false

partial def extractType : ffi.Type_ → extract llvm_type
| tp =>
  do id <- monadLift (ffi.getTypeTag tp);
     match id with
     | code.type.void      => pure (llvm_type.prim_type prim_type.void)
     | code.type.half      => pure (llvm_type.prim_type (prim_type.float_type float_type.half))
     | code.type.float     => pure (llvm_type.prim_type (prim_type.float_type float_type.float))
     | code.type.double    => pure (llvm_type.prim_type (prim_type.float_type float_type.double))
     | code.type.x86_fp80  => pure (llvm_type.prim_type (prim_type.float_type float_type.x86_fp80))
     | code.type.fp128     => pure (llvm_type.prim_type (prim_type.float_type float_type.fp128))
     | code.type.ppc_fp128 => pure (llvm_type.prim_type (prim_type.float_type float_type.ppc_fp128))
     | code.type.label     => pure (llvm_type.prim_type prim_type.label)
     | code.type.metadata  => pure (llvm_type.prim_type prim_type.metadata)
     | code.type.x86_mmx   => pure (llvm_type.prim_type prim_type.x86mmx)
     | code.type.token     => pure (llvm_type.prim_type prim_type.token)

     | code.type.integer =>
          do n <- monadLift (ffi.getIntegerTypeWidth tp);
             pure (llvm_type.prim_type (prim_type.integer n))

     | code.type.function =>
          do dt <- monadLift (ffi.getFunctionTypeData tp);
             match dt with
             | some (ret, args, varargs) =>
                 do ret' <- extractType ret;
                    args' <- Array.mapM extractType args;
                    pure (llvm_type.fun_ty ret' args' varargs)
             | none => throw (IO.userError "expected function type!")

     | code.type.struct =>
          do tn <- monadLift (ffi.getTypeName tp);
             match tn with

             -- named struct type, check if we need to traverse the type definition
             | some nm => 
               do alreadyVisited <- extract.visit nm;
                  -- only recurse into the definition if this is the first time
                  -- we've encountered this named type
                  unless alreadyVisited
                     (do opq <- monadLift (ffi.typeIsOpaque tp);
                         match opq with
                         | true => extract.define nm type_decl_body.opaque
                         | false =>
                             do dt <- monadLift (ffi.getStructTypeData tp);
                                match dt with
                                | some (packed, tps) => 
                                    do tps' <- Array.mapM extractType tps;
                                       extract.define nm (type_decl_body.defn (llvm_type.struct packed tps'))
                                | none => throw (IO.userError "expected struct type!"));
                  pure (llvm_type.alias nm)

             -- literal struct type, recurse into it's definition
             | none =>
               do dt <- monadLift (ffi.getStructTypeData tp);
                  match dt with
                  | some (packed, tps)  => llvm_type.struct packed <$> Array.mapM extractType tps
                  | none => throw (IO.userError "expected struct type!")

     | code.type.array =>
          do dt <- monadLift (ffi.getSequentialTypeData tp);
             match dt with
             | some (n, el) => llvm_type.array n <$> extractType el
             | none => throw (IO.userError "expected array type!")
     | code.type.pointer =>
          do eltp <- monadLift (ffi.getPointerElementType tp);
             match eltp with
             | none => throw (IO.userError "expected pointer type!")
             | (some x) => llvm_type.ptr_to <$> extractType x
     | code.type.vector =>
          do dt <- monadLift (ffi.getSequentialTypeData tp);
             match dt with
             | some (n, el) => llvm_type.vector n <$> extractType el
             | none => throw (IO.userError "expected vector type!")

@[reducible]
def instrMap := RBMap ffi.Instruction ident ffi.instructionLt

@[reducible]
def bbMap := RBMap ffi.BasicBlock block_label ffi.basicBlockLt


structure value_context :=
  (fun_args : Array (typed ident))
  (imap : instrMap)
  (bmap : bbMap)

def empty_value_context := value_context.mk Array.empty RBMap.empty RBMap.empty


def extractArgs (fn : ffi.Function) : extract (Nat × Array (typed ident)) :=
  do rawargs <- monadLift (ffi.getFunctionArgs fn);
     Array.iterateM rawargs (0, Array.empty) (λ _ a b => do
       let (mnm, rawtp) := a;
       let (counter, args) := b;
       tp <- extractType rawtp;
       match mnm with
       | none      => pure (counter+1, Array.push args (typed.mk tp (ident.anon counter)))
       | (some nm) => pure (counter,   Array.push args (typed.mk tp (ident.named nm)))
     )


def extractBBLabel (bb:ffi.BasicBlock) (c:Nat) : extract (Nat × block_label) :=
  do nm <- monadLift (ffi.getBBName bb);
     match nm with
     | none      => pure (c+1, block_label.mk (ident.anon c))
     | (some nm) => pure (c  , block_label.mk (ident.named nm))

def computeInstructionNumbering (rawbb:ffi.BasicBlock) (c0:Nat) (imap0:instrMap) : extract (Nat × instrMap) :=
  do instrarr <- monadLift (ffi.getInstructionArray rawbb);
     Array.iterateM instrarr (c0, imap0)
       (λ _ rawi st =>
         do let (c,imap) := st;
            tp <- monadLift (ffi.getInstructionType rawi);
            isv <- monadLift (typeIsVoid tp);
            if isv then
              pure (c,imap)
            else
              do mnm <- monadLift (ffi.getInstructionName rawi);
                 match mnm with
                 | (some nm) => pure (c, RBMap.insert imap rawi (ident.named nm))
                 | none      => pure (c+1, RBMap.insert imap rawi (ident.anon c))
       )

def computeNumberings (c0:Nat) (fn:ffi.Function) : extract (bbMap × instrMap) :=
  do bbarr <- monadLift (ffi.getBasicBlockArray fn);
     (_,finalbmap, finalimap) <-
       Array.iterateM bbarr (c0, (RBMap.empty : bbMap), (RBMap.empty : instrMap))
         (λ_ rawbb st =>
            do let (c, bmap, imap) := st;
               (c', blab) <- extractBBLabel rawbb c;
               bmap' <- pure (RBMap.insert bmap rawbb blab);
               (c'', imap') <- computeInstructionNumbering rawbb c' imap;
               pure (c'',bmap',imap')
            );
     pure (finalbmap, finalimap).

partial def extractConstant : ffi.Constant -> extract value
| rawc =>
  do let extractTypedConstant (c:ffi.Constant) : extract (typed value) :=
            (do tp <- monadLift (ffi.getValueType c) >>= extractType;
                x  <- extractConstant c;
                pure (typed.mk tp x));

     tag <- monadLift (ffi.getConstantTag rawc);
     match tag with
     | code.const.ConstantInt =>
       do d <- monadLift (ffi.getConstIntData rawc);
          match d with
          | some (_w, v) => pure (value.integer (Int.ofNat v))
          | none => throw (IO.userError "expected constant integer value")
     | code.const.Function =>
        do nm <- monadLift (ffi.getConstantName rawc);
           match nm with
           | some s => pure (value.symbol (symbol.mk s))
           | none   => throw (IO.userError "expected function value")
     | code.const.GlobalVariable =>
        do nm <- monadLift (ffi.getConstantName rawc);
           match nm with
           | some s => pure (value.symbol (symbol.mk s))
           | none   => throw (IO.userError "expected global variable")

     | code.const.ConstantPointerNull => pure value.null

     | code.const.ConstantDataArray =>
        do md <- monadLift (ffi.getConstArrayData rawc);
           match md with
           | none => throw (IO.userError "expected constant array")
           | some (elty, cs) => 
                do elty' <- extractType elty;
                   cs' <- cs.mapM extractConstant;
                   pure (value.array elty' cs')

     | code.const.ConstantExpr =>
        do md <- monadLift (ffi.getConstExprData rawc);
           match md with
           | none => throw (IO.userError "expected constant expression")
           | some (op, xs) =>
             match op with
             | code.instr.GetElementPtr =>
                  do cs <- Array.mapM extractTypedConstant xs;
                     pure (value.const_expr (const_expr.gep false none (llvm_type.prim_type prim_type.void) cs))

             | _ => throw (IO.userError ("unexpected (or unimplemented) constant instruction opcode: " ++ op.asString))
     | _ => throw (IO.userError ("unknown constant value: " ++ tag.asString))

def extractValue (ctx:value_context) (rawv:ffi.Value) : extract value :=
  do decmp <- monadLift (ffi.decomposeValue rawv);
     match decmp with
     | ffi.value_decomposition.argument_value n =>
       (match Array.get? ctx.fun_args n with
        | none => throw (IO.userError "invalid argument value")
        | (some i) => pure (value.ident i.value))
     | ffi.value_decomposition.instruction_value i =>
       (match RBMap.find ctx.imap i with
        | none => throw (IO.userError "invalid instruction value")
        | (some i) => pure (value.ident i)
       )

     | ffi.value_decomposition.constant_value c => extractConstant c

     | ffi.value_decomposition.block_value b =>
          throw (IO.userError "unimplemented: basic block value")

     | ffi.value_decomposition.unknown_value => throw (IO.userError "unknown value")

def extractBlockLabel (ctx:value_context) (bb:ffi.BasicBlock) : extract block_label :=
  match RBMap.find ctx.bmap bb with
  | none => throw (IO.userError "unknown basic block")
  | (some lab) => pure lab

def extractTypedValue (ctx:value_context) (rawv:ffi.Value) : extract (typed value) :=
  do tp <- monadLift (ffi.getValueType rawv) >>= extractType;
     v  <- extractValue ctx rawv;
     pure (typed.mk tp v)

def extractBinaryOp (rawInstr:ffi.Instruction) (ctx:value_context) (f:typed value → value → instruction) : extract instruction :=
  do x <- monadLift (ffi.getBinaryOperatorValues rawInstr);
     match x with
     | none => throw (IO.userError "expected binary operation")
     | some (o1,o2) =>
        do v1 <- extractTypedValue ctx o1;
           v2 <- extractTypedValue ctx o2;
           pure (f v1 v2.value)

def extractCastOp (rawinstr:ffi.Instruction) (ctx:value_context) (f:typed value → llvm_type → instruction) : extract instruction :=
  do x <- monadLift (ffi.getCastInstData rawinstr);
     match x with
     | none => throw (IO.userError "expected conversion instruction")
     | some (_op, v) =>
         do tv <- extractTypedValue ctx v;
            outty <- monadLift (ffi.getInstructionType rawinstr) >>= extractType;
            pure (f tv outty)

def extractICmpOp (n:code.icmp) : icmp_op :=
  match n with
  | code.icmp.eq  => icmp_op.ieq
  | code.icmp.ne  => icmp_op.ine
  | code.icmp.ugt => icmp_op.iugt
  | code.icmp.uge => icmp_op.iuge
  | code.icmp.ult => icmp_op.iult
  | code.icmp.ule => icmp_op.iule
  | code.icmp.sgt => icmp_op.isgt
  | code.icmp.sge => icmp_op.isge
  | code.icmp.slt => icmp_op.islt
  | code.icmp.sle => icmp_op.isle


def extractInstruction (rawinstr:ffi.Instruction) (ctx:value_context) : extract instruction :=
  do op <- monadLift (ffi.getInstructionOpcode rawinstr);
     tp <- monadLift (ffi.getInstructionType rawinstr) >>= extractType;
     match op with
     -- == terminators ==
     -- return
     | code.instr.Ret =>
            do mv <- monadLift (ffi.getInstructionReturnValue rawinstr);
               match mv with
               | none => pure instruction.ret_void
               | some v =>
                  do tyv <- extractTypedValue ctx v;
                     pure (instruction.ret tyv)

     -- br
     | code.instr.Br =>
        do d <- monadLift (ffi.getBranchInstData rawinstr);
           match d with
           | none => throw (IO.userError "expected branch instruction")
           | some (ffi.branch_decomposition.unconditional b) =>
               instruction.jump <$> extractBlockLabel ctx b
           | some (ffi.branch_decomposition.conditional c t f) =>
               do cv <- extractTypedValue ctx c;
                  tl <- extractBlockLabel ctx t;
                  fl <- extractBlockLabel ctx f;
                  pure (instruction.br cv tl fl)

     -- unreachable
     | code.instr.Unreachable => pure instruction.unreachable

     -- == binary operators ==
     -- add
     | code.instr.Add =>
        do uov <- monadLift (ffi.hasNoUnsignedWrap rawinstr);
           sov <- monadLift (ffi.hasNoSignedWrap rawinstr);
           extractBinaryOp rawinstr ctx (instruction.arith (arith_op.add uov sov))
     -- fadd
     | code.instr.FAdd => extractBinaryOp rawinstr ctx (instruction.arith arith_op.fadd)
     -- sub
     | code.instr.Sub =>
        do uov <- monadLift (ffi.hasNoUnsignedWrap rawinstr);
           sov <- monadLift (ffi.hasNoSignedWrap rawinstr);
           extractBinaryOp rawinstr ctx (instruction.arith (arith_op.sub uov sov))
     -- fsub
     | code.instr.FSub => extractBinaryOp rawinstr ctx (instruction.arith arith_op.fsub)
     -- mul
     | code.instr.Mul =>
        do uov <- monadLift (ffi.hasNoUnsignedWrap rawinstr);
           sov <- monadLift (ffi.hasNoSignedWrap rawinstr);
           extractBinaryOp rawinstr ctx (instruction.arith (arith_op.mul uov sov))
     -- fmul
     | code.instr.FMul => extractBinaryOp rawinstr ctx (instruction.arith arith_op.fmul)
     -- udiv
     | code.instr.UDiv =>
        do ex <- monadLift (ffi.isExact rawinstr);
           extractBinaryOp rawinstr ctx (instruction.arith (arith_op.udiv ex))
     -- sdiv
     | code.instr.SDiv =>
        do ex <- monadLift (ffi.isExact rawinstr);
           extractBinaryOp rawinstr ctx (instruction.arith (arith_op.sdiv ex))
     -- fdiv
     | code.instr.FDiv => extractBinaryOp rawinstr ctx (instruction.arith arith_op.fdiv)
     -- urem
     | code.instr.URem => extractBinaryOp rawinstr ctx (instruction.arith arith_op.urem)
     -- srem
     | code.instr.SRem => extractBinaryOp rawinstr ctx (instruction.arith arith_op.srem)
     -- frem
     | code.instr.FRem => extractBinaryOp rawinstr ctx (instruction.arith arith_op.frem)

     -- shl
     | code.instr.Shl =>
         do uov <- monadLift (ffi.hasNoUnsignedWrap rawinstr);
            sov <- monadLift (ffi.hasNoSignedWrap rawinstr);
            extractBinaryOp rawinstr ctx (instruction.bit (bit_op.shl uov sov))
     -- lshr
     | code.instr.LShr =>
         do ex <- monadLift (ffi.isExact rawinstr);
            extractBinaryOp rawinstr ctx (instruction.bit (bit_op.lshr ex))
     -- ashr
     | code.instr.AShr =>
         do ex <- monadLift (ffi.isExact rawinstr);
            extractBinaryOp rawinstr ctx (instruction.bit (bit_op.ashr ex))
     -- and
     | code.instr.And => extractBinaryOp rawinstr ctx (instruction.bit bit_op.and)
     -- or
     | code.instr.Or => extractBinaryOp rawinstr ctx (instruction.bit bit_op.or)
     -- xor
     | code.instr.Xor => extractBinaryOp rawinstr ctx (instruction.bit bit_op.xor)

     -- alloca
     | code.instr.Alloca =>
       do md ← monadLift (ffi.getAllocaData rawinstr);
          match md with
          | none => throw (IO.userError "Expected alloca instruction")
          | (some (tp, nelts, align)) =>
            do tp' <- extractType tp;
               nelts' <- Option.mapM (extractTypedValue ctx) nelts;
               pure (instruction.alloca tp' nelts' align)

     -- load
     | code.instr.Load =>
       do md ← monadLift (ffi.getLoadData rawinstr);
          match md with
          | none => throw (IO.userError "Expected load instruction")
          | (some (ptr, align)) =>
            do ptr' <- extractTypedValue ctx ptr;
               pure (instruction.load ptr' none align) -- TODO atomic ordering

     -- store
     | code.instr.Store =>
       do md ← monadLift (ffi.getStoreData rawinstr);
          match md with
          | none => throw (IO.userError "Expected store instruction")
          | (some (val,ptr,align)) =>
           do val' <- extractTypedValue ctx val;
              ptr' <- extractTypedValue ctx ptr;
              pure (instruction.store val' ptr' align)

     -- GEP
     | code.instr.GetElementPtr =>
        do md <- monadLift (ffi.getGEPData rawinstr);
           match md with
           | none => throw (IO.userError "Expected GEP instruction")
           | (some (inbounds,base,idxes)) =>
             do base' <- extractTypedValue ctx base;
                idxes' <- Array.mapM (extractTypedValue ctx) idxes;
                pure (instruction.gep inbounds base' idxes')

     -- trunc
     | code.instr.Trunc => extractCastOp rawinstr ctx (instruction.conv conv_op.trunc)
     -- zext
     | code.instr.ZExt => extractCastOp rawinstr ctx (instruction.conv conv_op.zext)
     -- sext
     | code.instr.SExt => extractCastOp rawinstr ctx (instruction.conv conv_op.sext)
     -- fptoui
     | code.instr.FPToUI => extractCastOp rawinstr ctx (instruction.conv conv_op.fp_to_ui)
     -- fptosi
     | code.instr.FPToSI => extractCastOp rawinstr ctx (instruction.conv conv_op.fp_to_si)
     -- uitofp
     | code.instr.UIToFP => extractCastOp rawinstr ctx (instruction.conv conv_op.ui_to_fp)
     -- sitofp
     | code.instr.SIToFP => extractCastOp rawinstr ctx (instruction.conv conv_op.si_to_fp)
     -- fptrunc
     | code.instr.FPTrunc => extractCastOp rawinstr ctx (instruction.conv conv_op.fp_trunc)
     -- fpext
     | code.instr.FPExt => extractCastOp rawinstr ctx (instruction.conv conv_op.fp_ext)
     -- ptrtoint
     | code.instr.PtrToInt => extractCastOp rawinstr ctx (instruction.conv conv_op.ptr_to_int)
     -- inttoptr
     | code.instr.IntToPtr => extractCastOp rawinstr ctx (instruction.conv conv_op.int_to_ptr)
     -- bitcast
     | code.instr.BitCast => extractCastOp rawinstr ctx (instruction.conv conv_op.bit_cast)

     -- icmp
     | code.instr.ICmp =>
          do d <- monadLift (ffi.getICmpInstData rawinstr);
             match d with
             | none => throw (IO.userError "expected icmp instruction")
             | some (code, (v1, v2)) =>
               do o1 <- extractTypedValue ctx v1;
                  o2 <- extractTypedValue ctx v2;
                  let op := extractICmpOp code;
                  pure (instruction.icmp op o1 o2.value)

     -- PHI
     | code.instr.PHI =>
          do t <- monadLift (ffi.getInstructionType rawinstr) >>= extractType;
             d <- monadLift (ffi.getPhiData rawinstr);
             match d with
             | none => throw (IO.userError "expected phi instruction")
             | some vs =>
                 do vs' <- vs.mapM (λ (vbb: ffi.Value × ffi.BasicBlock) =>
                             Prod.mk <$> extractValue ctx vbb.1 <*> extractBlockLabel ctx vbb.2);
                    pure (instruction.phi t vs')

     -- call
     | code.instr.Call =>
          do d <- monadLift (ffi.getCallInstData rawinstr);
             match d with
             | none => throw (IO.userError "expected call instruction")
             | some (tail,retty,funv,args) =>
                 do retty' <- extractType retty;
                    let retty'' := match retty' with
                                   | llvm_type.prim_type prim_type.void => @none llvm_type
                                   | _ => some (retty');
                    funv'  <- extractTypedValue ctx funv;
                    args'  <- Array.mapM (extractTypedValue ctx) args;
                    pure (instruction.call tail retty'' funv'.value args')

     -- select
     | code.instr.Select =>
          do d <- monadLift (ffi.getSelectInstData rawinstr);
             match d with
             | none => throw (IO.userError "expected select instruction")
             | (some (vc, (vt,ve))) =>
                do c <- extractTypedValue ctx vc;
                   t <- extractTypedValue ctx vt;
                   e <- extractTypedValue ctx ve;
                   pure (instruction.select c t e.value)

     | _ => throw (IO.userError ("unimplemented instruction opcode: " ++ op.asString))
.

def extractStmt (rawinstr:ffi.Instruction) (ctx:value_context) : extract stmt :=
  do i <- extractInstruction rawinstr ctx;
     pure (stmt.mk (RBMap.find ctx.imap rawinstr) i Array.empty).

def extractStatements (bb:ffi.BasicBlock) (ctx:value_context) : extract (Array stmt) :=
  do rawinstrs <- monadLift (ffi.getInstructionArray bb);
     Array.iterateM rawinstrs Array.empty (λ_ rawinstr stmts =>
       do stmt <- extractStmt rawinstr ctx;
          pure (Array.push stmts stmt)).

def extractBasicBlocks (fn : ffi.Function) (ctx:value_context) : extract (Array basic_block) :=
  do rawbbs <- monadLift (ffi.getBasicBlockArray fn);
     Array.iterateM rawbbs Array.empty (λ_ rawbb bs =>
       match RBMap.find ctx.bmap rawbb with
       | none => throw (IO.userError "unknown basic block")
       | some lab =>
           do stmts <- extractStatements rawbb ctx;
              pure (Array.push bs (basic_block.mk lab stmts))
       ).

def extractFunction (fn : ffi.Function) : extract define :=
  do nm <- monadLift (ffi.getFunctionName fn);
     ret <- monadLift (ffi.getReturnType fn) >>= extractType;
     (counter, args) <- extractArgs fn;
     (bmap, imap) <- computeNumberings counter fn;

     bbs <- extractBasicBlocks fn (value_context.mk args imap bmap);

     pure (define.mk
            none -- linkage
            ret
            (symbol.mk nm)
            args
            false -- varargs
            Array.empty -- attrs
            none -- section
            none -- gc
            bbs
            (strmap_empty _) -- metadata
            none -- comdat
          ).

def extractDataLayout (m:ffi.Module) : IO (List layout_spec) :=
  do dlstr <- ffi.getModuleDataLayoutStr m;
     match parse.run parse.data_layout dlstr with
     | (Sum.inl (stk,str')) =>
          throw (IO.userError ("Could not parse data layout string: " ++ dlstr ++ "  " ++ stk.repr ++ "  " ++ str'))
     | (Sum.inr dl) => pure dl.

def extractGlobal (g:ffi.GlobalVar) : extract global :=
  do tp <- monadLift (ffi.getValueType g) >>= extractType;
     match tp with
     | llvm_type.ptr_to valtp =>
       do md <- monadLift (ffi.getGlobalVarData g);
          match md with
          | none => throw (IO.userError "Expected global variable")
          | some (nm, val, align) =>
              do val' <- val.mapM (extractValue empty_value_context);
                 -- TODO!
                 let attrs := global_attrs.mk none none false;
                 pure (global.mk (symbol.mk nm) attrs valtp val' align (strmap_empty _))
     | _ => throw (IO.userError ("Expected pointer type for global but got: " ++ (pp.render (pp_type tp))))

def extractModule (m:ffi.Module) : extract module :=
  do nm <- monadLift (ffi.getModuleIdentifier m);
     dl <- monadLift (extractDataLayout m);
     fns <- monadLift (ffi.getFunctionArray m) >>= Array.mapM extractFunction;
     gs <- monadLift (ffi.getGlobalArray m) >>= Array.mapM extractGlobal;
     pure (module.mk
             (some nm)
             dl
             Array.empty -- types TODO
             Array.empty -- named_md TODO
             Array.empty -- unnamed_md TODO
             (strmap_empty _) -- comdat TODO
             gs
             Array.empty -- declares TODO
             fns -- defines
             Array.empty -- inline ASM TODO,
             Array.empty -- global alises TODO
           ).


def toTypeDecl (x:String × type_decl_body) : type_decl :=
  type_decl.mk x.1 x.2.

def loadModule (m:ffi.Module) : IO module :=
  do (am, mod) <- (extractModule m).run;
     let tds := List.map toTypeDecl (am.toList);
     pure { mod with types := tds.toArray }

end llvm.
