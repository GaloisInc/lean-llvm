import init.data.array
import init.data.int
import init.data.rbmap

import .ast
import .pp
import .parser
import .data_layout
import .llvm_ffi

namespace Option
  universes u v.

  def mmap {m:Type u → Type v} {α β:Type u} [Applicative m] (f:α → m β) : Option α → m (Option β)
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

def typeIsVoid (tp : LLVMType) : IO Bool :=
  do id <- getTypeTag tp;
     match id with
     | code.type.void => pure true
     | _ => pure false

partial def extractType : LLVMType → IO llvm_type
| tp =>
  do id <- getTypeTag tp;
     match id with
     | code.type.void => pure (llvm_type.prim_type prim_type.void)
     | code.type.half => pure (llvm_type.prim_type (prim_type.float_type float_type.half))
     | code.type.float => pure (llvm_type.prim_type (prim_type.float_type float_type.float))
     | code.type.double => pure (llvm_type.prim_type (prim_type.float_type float_type.double))
     | code.type.x86_fp80 => pure (llvm_type.prim_type (prim_type.float_type float_type.x86_fp80))
     | code.type.fp128 => pure (llvm_type.prim_type (prim_type.float_type float_type.fp128))
     | code.type.ppc_fp128 => pure (llvm_type.prim_type (prim_type.float_type float_type.ppc_fp128))
     | code.type.label => pure (llvm_type.prim_type prim_type.label)
     | code.type.metadata => pure (llvm_type.prim_type prim_type.metadata)
     | code.type.x86_mmx => pure (llvm_type.prim_type prim_type.x86mmx)
     | code.type.token => pure (llvm_type.opaque)
     | code.type.integer =>
          do n <- getIntegerTypeWidth tp;
             pure (llvm_type.prim_type (prim_type.integer n))
     | code.type.function =>
          do dt <- getFunctionTypeData tp;
             match dt with
             | some (ret, args, varargs) =>
                 do ret' <- extractType ret;
                    args' <- Array.mmap extractType args;
                    pure (llvm_type.fun_ty ret' args' varargs)
             | none => throw (IO.userError "expected function type!")
     | code.type.struct =>
          do dt <- getStructTypeData tp;
             match dt with
             | some (true, tps)  => llvm_type.packed_struct <$> Array.mmap extractType tps
             | some (false, tps) => llvm_type.struct <$> Array.mmap extractType tps
             | none => throw (IO.userError "expected struct type!")
     | code.type.array =>
          do dt <- getSequentialTypeData tp;
             match dt with
             | some (n, el) => llvm_type.array n <$> extractType el
             | none => throw (IO.userError "expected array type!")
     | code.type.pointer =>
          do eltp <- getPointerElementType tp;
             match eltp with
             | none => throw (IO.userError "expected pointer type!")
             | (some x) => llvm_type.ptr_to <$> extractType x
     | code.type.vector =>
          do dt <- getSequentialTypeData tp;
             match dt with
             | some (n, el) => llvm_type.vector n <$> extractType el
             | none => throw (IO.userError "expected vector type!")

@[reducible]
def instrMap := RBMap Instruction ident instructionLt

@[reducible]
def bbMap := RBMap BasicBlock block_label basicBlockLt


structure value_context :=
  (fun_args : Array (typed ident))
  (imap : instrMap)
  (bmap : bbMap)

def extractArgs (fn : LLVMFunction) : IO (Nat × Array (typed ident)) :=
  do rawargs <- getFunctionArgs fn;
     Array.miterate rawargs (0, Array.empty) (λ _ a b => do
       let (mnm, rawtp) := a;
       let (counter, args) := b;
       tp <- extractType rawtp;
       match mnm with
       | none      => pure (counter+1, Array.push args (typed.mk tp (ident.anon counter)))
       | (some nm) => pure (counter,   Array.push args (typed.mk tp (ident.named nm)))
     )


def extractBBLabel (bb:BasicBlock) (c:Nat) : IO (Nat × block_label) :=
  do nm <- getBBName bb;
     match nm with
     | none      => pure (c+1, block_label.anon c)
     | (some nm) => pure (c  , block_label.named nm)

def computeInstructionNumbering (rawbb:BasicBlock) (c0:Nat) (imap0:instrMap) : IO (Nat × instrMap) :=
  do instrarr <- getInstructionArray rawbb;
     Array.miterate instrarr (c0, imap0)
       (λ _ rawi st =>
         do let (c,imap) := st;
            tp <- getInstructionType rawi;
            isv <- typeIsVoid tp;
            if isv then
              pure (c,imap)
            else
              do mnm <- getInstructionName rawi;
                 match mnm with
                 | (some nm) => pure (c, RBMap.insert imap rawi (ident.named nm))
                 | none      => pure (c+1, RBMap.insert imap rawi (ident.anon c))
       )

def computeNumberings (c0:Nat) (fn:LLVMFunction) : IO (bbMap × instrMap) :=
  do bbarr <- getBasicBlockArray fn;
     (_,finalbmap, finalimap) <-
       Array.miterate bbarr (c0, (RBMap.empty : bbMap), (RBMap.empty : instrMap))
         (λ_ rawbb st =>
            do let (c, bmap, imap) := st;
               (c', blab) <- extractBBLabel rawbb c;
               bmap' <- pure (RBMap.insert bmap rawbb blab);
               (c'', imap') <- computeInstructionNumbering rawbb c' imap;
               pure (c'',bmap',imap')
         );
     pure (finalbmap, finalimap).

def extractConstant (rawc:LLVMConstant) : IO value :=
  do tag <- getConstantTag rawc;
     match tag with
     | code.const.ConstantInt =>
       do d <- getConstIntData rawc;
          match d with
          | some (_w, v) => pure (value.integer (Int.ofNat v))
          | none => throw (IO.userError "expected constant integer value")
     | code.const.Function =>
        do nm <- getConstantName rawc;
           match nm with
           | some s => pure (value.symbol (symbol.mk s))
           | none   => throw (IO.userError "expected function value")
     | code.const.GlobalVariable =>
        do nm <- getConstantName rawc;
           match nm with
           | some s => pure (value.symbol (symbol.mk s))
           | none   => throw (IO.userError "expected global variable")

     | _ => throw (IO.userError ("unknown constant value: " ++ tag.asString))

def extractValue (ctx:value_context) (rawv:LLVMValue) : IO value :=
  do decmp <- decomposeValue rawv;
     match decmp with
     | (value_decomposition.argument_value n) =>
       (match Array.getOpt ctx.fun_args n with
        | none => throw (IO.userError "invalid argument value")
        | (some i) => pure (value.ident i.value))
     | (value_decomposition.instruction_value i) =>
       (match RBMap.find ctx.imap i with
        | none => throw (IO.userError "invalid instruction value")
        | (some i) => pure (value.ident i)
       )

     | (value_decomposition.constant_value c) => extractConstant c

     | _ => throw (IO.userError "unknown value")

def extractBlockLabel (ctx:value_context) (bb:BasicBlock) : IO block_label :=
  match RBMap.find ctx.bmap bb with
  | none => throw (IO.userError "unknown basic block")
  | (some lab) => pure lab

def extractTypedValue (ctx:value_context) (rawv:LLVMValue) : IO (typed value) :=
  do tp <- getValueType rawv >>= extractType;
     v  <- extractValue ctx rawv;
     pure (typed.mk tp v)

def extractBinaryOp (rawInstr:Instruction) (ctx:value_context) (f:typed value → value → instruction) : IO instruction :=
  getBinaryOperatorValues rawInstr >>= λx =>
  match x with
  | none => throw (IO.userError "expected binary operation")
  | (some (o1,o2)) =>
     do v1 <- extractTypedValue ctx o1;
        v2 <- extractTypedValue ctx o2;
        pure (f v1 v2.value)


def extractCastOp (rawinstr:Instruction) (ctx:value_context) (f:typed value → llvm_type → instruction) : IO instruction :=
  getCastInstData rawinstr >>= λx =>
  match x with
  | none => throw (IO.userError "expected conversion instruction")
  | (some (_op, v)) =>
      do tv <- extractTypedValue ctx v;
         outty <- getInstructionType rawinstr >>= extractType;
         pure (f tv outty)

def extractICmpOp (n:code.icmp) : IO icmp_op :=
  match n with
  | code.icmp.eq => pure icmp_op.ieq
  | code.icmp.ne => pure icmp_op.ine
  | code.icmp.ugt => pure icmp_op.iugt
  | code.icmp.uge => pure icmp_op.iuge
  | code.icmp.ult => pure icmp_op.iult
  | code.icmp.ule => pure icmp_op.iule
  | code.icmp.sgt => pure icmp_op.isgt
  | code.icmp.sge => pure icmp_op.isge
  | code.icmp.slt => pure icmp_op.islt
  | code.icmp.sle => pure icmp_op.isle


def extractInstruction (rawinstr:Instruction) (ctx:value_context) : IO instruction :=
  do op <- getInstructionOpcode rawinstr;
     tp <- getInstructionType rawinstr >>= extractType;
     match op with
     -- == terminators ==
     -- return
     | code.instr.Ret =>
            do mv <- getInstructionReturnValue rawinstr;
               match mv with
               | none => pure instruction.ret_void
               | (some v) =>
                  do tyv <- extractTypedValue ctx v;
                     pure (instruction.ret tyv)

     -- br
     | code.instr.Br =>
        do d <- getBranchInstData rawinstr;
           match d with
           | none => throw (IO.userError "expected branch instruction")
           | (some (branch_decomposition.unconditional b)) =>
               instruction.jump <$> extractBlockLabel ctx b
           | (some (branch_decomposition.conditional c t f)) =>
               do cv <- extractTypedValue ctx c;
                  tl <- extractBlockLabel ctx t;
                  fl <- extractBlockLabel ctx f;
                  pure (instruction.br cv tl fl)

     -- unreachable
     | code.instr.Unreachable => pure instruction.unreachable

     -- == binary operators ==
     -- add
     | code.instr.Add =>
        do uov <- hasNoUnsignedWrap rawinstr;
           sov <- hasNoSignedWrap rawinstr;
           extractBinaryOp rawinstr ctx (instruction.arith (arith_op.add uov sov))
     -- fadd
     | code.instr.FAdd => extractBinaryOp rawinstr ctx (instruction.arith arith_op.fadd)
     -- sub
     | code.instr.Sub =>
        do uov <- hasNoUnsignedWrap rawinstr;
           sov <- hasNoSignedWrap rawinstr;
           extractBinaryOp rawinstr ctx (instruction.arith (arith_op.sub uov sov))
     -- fsub
     | code.instr.FSub => extractBinaryOp rawinstr ctx (instruction.arith arith_op.fsub)
     -- mul
     | code.instr.Mul =>
        do uov <- hasNoUnsignedWrap rawinstr;
           sov <- hasNoSignedWrap rawinstr;
           extractBinaryOp rawinstr ctx (instruction.arith (arith_op.mul uov sov))
     -- fmul
     | code.instr.FMul => extractBinaryOp rawinstr ctx (instruction.arith arith_op.fmul)
     -- udiv
     | code.instr.UDiv =>
        do ex <- isExact rawinstr;
           extractBinaryOp rawinstr ctx (instruction.arith (arith_op.udiv ex))
     -- sdiv
     | code.instr.SDiv =>
        do ex <- isExact rawinstr;
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
         do uov <- hasNoUnsignedWrap rawinstr;
            sov <- hasNoSignedWrap rawinstr;
            extractBinaryOp rawinstr ctx (instruction.bit (bit_op.shl uov sov))
     -- lshr
     | code.instr.LShr =>
         do ex <- isExact rawinstr;
            extractBinaryOp rawinstr ctx (instruction.bit (bit_op.lshr ex))
     -- ashr
     | code.instr.AShr =>
         do ex <- isExact rawinstr;
            extractBinaryOp rawinstr ctx (instruction.bit (bit_op.ashr ex))
     -- and
     | code.instr.And => extractBinaryOp rawinstr ctx (instruction.bit bit_op.and)
     -- or
     | code.instr.Or => extractBinaryOp rawinstr ctx (instruction.bit bit_op.or)
     -- xor
     | code.instr.Xor => extractBinaryOp rawinstr ctx (instruction.bit bit_op.xor)

     -- alloca
     | code.instr.Alloca =>
       do md ← getAllocaData rawinstr;
          match md with
          | none => throw (IO.userError "Expected alloca instruction")
          | (some (tp, nelts, align)) =>
            do tp' <- extractType tp;
               nelts' <- Option.mmap (extractTypedValue ctx) nelts;
               pure (instruction.alloca tp' nelts' align)

     -- load
     | code.instr.Load =>
       do md ← getLoadData rawinstr;
          match md with
          | none => throw (IO.userError "Expected load instruction")
          | (some (ptr, align)) =>
            do ptr' <- extractTypedValue ctx ptr;
               pure (instruction.load ptr' none align) -- TODO atomic ordering

     -- store
     | code.instr.Store =>
       do md ← getStoreData rawinstr;
          match md with
          | none => throw (IO.userError "Expected store instruction")
          | (some (val,ptr,align)) =>
           do val' <- extractTypedValue ctx val;
              ptr' <- extractTypedValue ctx ptr;
              pure (instruction.store val' ptr' align)

     -- GEP
     | code.instr.GetElementPtr =>
        do md <- getGEPData rawinstr;
           match md with
           | none => throw (IO.userError "Expected GEP instruction")
           | (some (inbounds,base,idxes)) =>
             do base' <- extractTypedValue ctx base;
                idxes' <- Array.mmap (extractTypedValue ctx) idxes;
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
          do d <- getICmpInstData rawinstr;
             match d with
             | none => throw (IO.userError "expected icmp instruction")
             | (some (code, (v1, v2))) =>
               do o1 <- extractTypedValue ctx v1;
                  o2 <- extractTypedValue ctx v2;
                  op <- extractICmpOp code;
                  pure (instruction.icmp op o1 o2.value)

     -- PHI
     | code.instr.PHI =>
          do t <- getInstructionType rawinstr >>= extractType;
             d <- getPhiData rawinstr;
             match d with
             | none => throw (IO.userError "expected phi instruction")
             | some vs =>
                 do vs' <- vs.mmap (λ (vbb: LLVMValue×BasicBlock) =>
                            Prod.mk <$> extractValue ctx vbb.1 <*> extractBlockLabel ctx vbb.2);
                    pure (instruction.phi t vs')

     -- call
     | code.instr.Call =>
          do d <- getCallInstData rawinstr;
             match d with
             | none => throw (IO.userError "expected call instruction")
             | some (tail,retty,funv,args) =>
                 do retty' <- extractType retty;
                    let retty'' := match retty' with
                                   | llvm_type.prim_type prim_type.void => @none llvm_type
                                   | _ => some (retty');
                    funv'  <- extractTypedValue ctx funv;
                    args'  <- Array.mmap (extractTypedValue ctx) args;
                    pure (instruction.call tail retty'' funv'.value args')

     -- select
     | code.instr.Select =>
          do d <- getSelectInstData rawinstr;
             match d with
             | none => throw (IO.userError "expected select instruction")
             | (some (vc, (vt,ve))) =>
                do c <- extractTypedValue ctx vc;
                   t <- extractTypedValue ctx vt;
                   e <- extractTypedValue ctx ve;
                   pure (instruction.select c t e.value)

     | _ => throw (IO.userError ("unimplemented instruction opcode: " ++ op.asString))
.

def extractStmt (rawinstr:Instruction) (ctx:value_context) : IO stmt :=
  do i <- extractInstruction rawinstr ctx;
     pure (stmt.mk (RBMap.find ctx.imap rawinstr) i Array.empty).

def extractStatements (bb:BasicBlock) (ctx:value_context) : IO (Array stmt) :=
  do rawinstrs <- getInstructionArray bb;
     Array.miterate rawinstrs Array.empty (λ_ rawinstr stmts =>
       do stmt <- extractStmt rawinstr ctx;
          pure (Array.push stmts stmt)).

def extractBasicBlocks (fn : LLVMFunction) (ctx:value_context) : IO (Array basic_block) :=
  do rawbbs <- getBasicBlockArray fn;
     Array.miterate rawbbs Array.empty (λ_ rawbb bs =>
       match RBMap.find ctx.bmap rawbb with
       | none => throw (IO.userError "unknown basic block")
       | (some lab) =>
           do stmts <- extractStatements rawbb ctx;
              pure (Array.push bs (basic_block.mk lab stmts))
       ).

def extractFunction (fn : LLVMFunction) : IO define :=
  do nm <- getFunctionName fn;
     ret <- getReturnType fn >>= extractType;
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

def extractDataLayout (m:Module) : IO (List layout_spec) :=
  do dlstr <- getModuleDataLayoutStr m;
     match parse.run parse.data_layout dlstr with
     | (Sum.inl (stk,str')) =>
          throw (IO.userError ("Could not parse data layout string: " ++ dlstr ++ "  " ++ stk.repr ++ "  " ++ str'))
     | (Sum.inr dl) => pure dl.

def extractModule (m:Module) : IO module :=
  do nm <- getModuleIdentifier m;
     dl <- extractDataLayout m;
     fns <- getFunctionArray m >>= Array.mmap extractFunction;
     pure (module.mk
             (some nm)
             dl
             Array.empty -- types TODO
             Array.empty -- named_md TODO
             Array.empty -- unnamed_md TODO
             (strmap_empty _) -- comdat TODO
             Array.empty -- globals TODO
             Array.empty -- declares TODO
             fns -- defines
             Array.empty -- inline ASM TODO,
             Array.empty -- global alises TODO
           ).

end llvm.
