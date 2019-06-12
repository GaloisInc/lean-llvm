import init.data.array
import init.data.int
import init.data.rbmap

import .ast
import .pp

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

constant LLVMContext := Unit
constant MemoryBuffer := Unit
constant Module := Unit
constant LLVMFunction := Unit
constant LLVMType := Unit
constant BasicBlock := Unit
constant Instruction := Unit
constant LLVMValue := Unit
constant LLVMConstant := Unit

inductive value_decomposition 
| unknown_value  : value_decomposition
| argument_value : ℕ -> value_decomposition
| instruction_value : Instruction -> value_decomposition
| constant_value : LLVMConstant -> value_decomposition
.

/-- This constructs a LLVM Context and frees it when done. -/
@[extern 1 cpp "lean_llvm::newLLVMContext"]
constant newLLVMContext : IO LLVMContext := default _

@[extern 2 cpp "lean_llvm::newMemoryBufferFromFile"]
def newMemoryBufferFromFile : String → IO MemoryBuffer := default _

@[extern 3 cpp "lean_llvm::parseBitcodeFile"]
def parseBitcodeFile : MemoryBuffer → LLVMContext → IO Module := default _

@[extern 2 cpp "lean_llvm::getModuleIdentifier"]
def getModuleIdentifier : Module → IO String := default _

@[extern 3 cpp "lean_llvm::setModuleIdentifier"]
def setModuleIdentifier : Module → String → IO Unit := default _

@[extern 1 cpp "lean_llvm::mkSomeList"]
def mkSomeList : @& Nat → List Nat := default _

@[extern 2 cpp "lean_llvm::getFunctionArray"]
def getFunctionArray : @& Module -> IO (Array LLVMFunction) := default _

@[extern 2 cpp "lean_llvm::getFunctionName"]
def getFunctionName : @& LLVMFunction -> IO String := default _

@[extern 2 cpp "lean_llvm::getReturnType"]
def getReturnType : @& LLVMFunction -> IO LLVMType := default _

@[extern 2 cpp "lean_llvm::getFunctionArgs"]
def getFunctionArgs : @& LLVMFunction -> IO (Array (Option String × LLVMType)) := default _

@[extern 2 cpp "lean_llvm::getBasicBlockArray"]
def getBasicBlockArray : @& LLVMFunction -> IO (Array BasicBlock) := default _

@[extern 2 cpp "lean_llvm::getBBName"]
def getBBName : @& BasicBlock -> IO (Option String) := default _

@[extern 2 cpp "lean_llvm::getTypeTag"]
def getTypeTag : @& LLVMType -> IO ℕ := default _

@[extern 2 cpp "lean_llvm::getIntegerTypeWidth"]
def getIntegerTypeWidth : @& LLVMType -> IO ℕ := default _

@[extern 2 cpp "lean_llvm::getInstructionArray"]
def getInstructionArray : @& BasicBlock -> IO (Array Instruction) := default _

@[extern 2 cpp "lean_llvm::instructionLt"]
def instructionLt : @& Instruction -> @&Instruction -> Bool := default _

@[extern 2 cpp "lean_llvm::basicBlockLt"]
def basicBlockLt : @& BasicBlock -> @& BasicBlock -> Bool := default _

@[extern 2 cpp "lean_llvm::getInstructionName"]
def getInstructionName : @& Instruction -> IO (Option String) := default _

@[extern 2 cpp "lean_llvm::getInstructionType"]
def getInstructionType : @& Instruction -> IO LLVMType := default _

@[extern 2 cpp "lean_llvm::getInstructionOpcode"]
def getInstructionOpcode : @& Instruction -> IO ℕ := default _

@[extern 2 cpp "lean_llvm::getInstructionReturnValue"]
def getInstructionReturnValue : @& Instruction -> IO (Option LLVMValue) := default _

@[extern 2 cpp "lean_llvm::getValueType"]
def getValueType : @& LLVMValue -> IO LLVMType := default _

@[extern 2 cpp "lean_llvm::getBinaryOperatorValues"]
def getBinaryOperatorValues : @& Instruction -> IO (Option (LLVMValue × LLVMValue)) := default _

@[extern 2 cpp "lean_llvm::hasNoSignedWrap"]
def hasNoSignedWrap : @& Instruction -> IO Bool := default _

@[extern 2 cpp "lean_llvm::hasNoUnsignedWrap"]
def hasNoUnsignedWrap : @& Instruction -> IO Bool := default _

@[extern 2 cpp "lean_llvm::isExact"]
def isExact : @& Instruction -> IO Bool := default _

@[extern 2 cpp "lean_llvm::decomposeValue"]
def decomposeValue : @& LLVMValue -> IO value_decomposition := default _

@[extern 2 cpp "lean_llvm::getCmpInstData"]
def getCmpInstData : @& Instruction -> IO (Option (ℕ × (LLVMValue × LLVMValue))) := default _

@[extern 2 cpp "lean_llvm::getSelectInstData"]
def getSelectInstData : @& Instruction -> IO (Option (LLVMValue × (LLVMValue × LLVMValue))) := default _

-- return bitwidth and value
@[extern 2 cpp "lean_llvm::getConstIntData"]
def getConstIntData : @& LLVMConstant -> IO (Option (ℕ × ℕ)) := default _

namespace llvm.

def anonIdent (n:ℕ) : ident :=
  ident.mk (Nat.toDigits 10 n).asString.

def typeIsVoid (tp : LLVMType) : IO Bool :=
  do id <-getTypeTag tp,
     match id with
     | 0 := pure true
     | _ := pure false
.

def extractType (tp : LLVMType) : IO llvm_type :=
  do id <- getTypeTag tp,
     match id with
     | 0 := pure (llvm_type.prim_type prim_type.void)
     | 1 := pure (llvm_type.prim_type (prim_type.float_type float_type.half))
     | 2 := pure (llvm_type.prim_type (prim_type.float_type float_type.float))
     | 3 := pure (llvm_type.prim_type (prim_type.float_type float_type.double))
     | 4 := pure (llvm_type.prim_type (prim_type.float_type float_type.x86_fp80))
     | 5 := pure (llvm_type.prim_type (prim_type.float_type float_type.fp128))
     | 6 := pure (llvm_type.prim_type (prim_type.float_type float_type.ppc_fp128))
     | 7 := pure (llvm_type.prim_type prim_type.label)
     | 8 := pure (llvm_type.prim_type prim_type.metadata)
     | 9 := pure (llvm_type.prim_type prim_type.x86mmx)
     | 10 := pure (llvm_type.opaque)
     | 11 := (do n <- getIntegerTypeWidth tp,
                 pure (llvm_type.prim_type (prim_type.integer n)))
     | 12 := pure llvm_type.opaque -- functions
     | 13 := pure llvm_type.opaque -- structures
     | 14 := pure llvm_type.opaque -- arrays
     | 15 := pure llvm_type.opaque -- pointers
     | 16 := pure llvm_type.opaque -- vectors
     | _  := pure llvm_type.opaque -- other...
.


@[reducible]
def instrMap := RBMap Instruction ident instructionLt.

@[reducible]
def bbMap := RBMap BasicBlock block_label basicBlockLt.


structure value_context :=
  (fun_args : Array (typed ident))
  (imap : instrMap)
  (bmap : bbMap).

def extractArgs (fn : LLVMFunction) : IO (ℕ × Array (typed ident)) :=
  do rawargs <- getFunctionArgs fn,
     Array.miterate rawargs (0, Array.empty) (λ_ a b, 
       let (mnm, rawtp) := a,
           (counter, args) := b in
       do tp <- extractType rawtp,
          match mnm with
          | none      := pure (counter+1, Array.push args (typed.mk tp (anonIdent counter)))
          | (some nm) := pure (counter,   Array.push args (typed.mk tp (ident.mk nm)))
     )
.

def extractBBLabel (bb:BasicBlock) (c:ℕ) : IO (ℕ × block_label) :=
  do nm <- getBBName bb,
     match nm with
     | none      := pure (c+1, block_label.anon c)
     | (some nm) := pure (c  , block_label.named (ident.mk nm)).

def computeInstructionNumbering (rawbb:BasicBlock) (c0:ℕ) (imap0:instrMap) : IO (ℕ × instrMap) :=
  do instrarr <- getInstructionArray rawbb,
     Array.miterate instrarr (c0, imap0)
       (λ _ rawi st,
         let (c,imap) := st in
         do tp <- getInstructionType rawi,
            isv <- typeIsVoid tp,
            if isv then pure (c,imap) else
            do mnm <- getInstructionName rawi,
               match mnm with
               | (some nm) := pure (c, RBMap.insert imap rawi (ident.mk nm))
               | none      := pure (c+1, RBMap.insert imap rawi (ident.mk (Nat.toDigits 10 c).asString))
       ).

def computeNumberings (c0:ℕ) (fn:LLVMFunction) : IO (bbMap × instrMap) :=
  do bbarr <- getBasicBlockArray fn,
     (_,finalbmap, finalimap) <-
       Array.miterate bbarr (c0, (RBMap.empty : bbMap), (RBMap.empty : instrMap))
         (λ_ rawbb st, 
            let (c, bmap, imap) := st in
            do (c', blab) <- extractBBLabel rawbb c,
               bmap' <- pure (RBMap.insert bmap rawbb blab),
               (c'', imap') <- computeInstructionNumbering rawbb c' imap,
               pure (c'',bmap',imap')
         ),
     pure (finalbmap, finalimap).

def extractConstant (rawc:LLVMConstant) : IO value :=
  do d <- getConstIntData rawc,
     (match d with
      | (some (_w, v)) := pure (value.integer (Int.ofNat v))
      | none := throw (IO.userError "unknown constant value"))

def extractValue (rawv:LLVMValue) (ctx:value_context) : IO value :=
  do decmp <- decomposeValue rawv,
     match decmp with
     | (value_decomposition.argument_value n) :=
       (match Array.getOpt ctx.fun_args n with
        | none := throw (IO.userError "invalid argument value")
        | (some i) := pure (value.ident i.value))

     | (value_decomposition.instruction_value i) :=
       (match RBMap.find ctx.imap i with
        | none := throw (IO.userError "invalid instruction value")
        | (some i) := pure (value.ident i)
       )

     | (value_decomposition.constant_value c) := extractConstant c 

     | _ := throw (IO.userError "unknown value")
.

def extractTypedValue (rawv:LLVMValue) (ctx:value_context) : IO (typed value) :=
  do tp <- getValueType rawv >>= extractType,
     v  <- extractValue rawv ctx,
     pure (typed.mk tp v)
 .

def extractBinaryOp (rawInstr:Instruction) (ctx:value_context) (f:typed value → value → instruction) : IO instruction :=
  getBinaryOperatorValues rawInstr >>= λx,
  match x with
  | none := throw (IO.userError "expected binary operation")
  | (some (o1,o2)) := 
     do v1 <- extractTypedValue o1 ctx,
        v2 <- extractTypedValue o2 ctx,
        pure (f v1 v2.value)
.


-- C.F. llvm/InstrTypes.h, enum Predicate
def extractICmpOp (n:ℕ) : IO icmp_op :=
  match n with
  | 32 := pure icmp_op.ieq
  | 33 := pure icmp_op.ine
  | 34 := pure icmp_op.iugt
  | 35 := pure icmp_op.iuge
  | 36 := pure icmp_op.iult
  | 37 := pure icmp_op.iule
  | 38 := pure icmp_op.isgt
  | 39 := pure icmp_op.isge
  | 40 := pure icmp_op.islt
  | 41 := pure icmp_op.isle
  | _  := throw (IO.userError ("unexpected icmp operation: " ++ (Nat.toDigits 10 n).asString))
.

def extractInstruction (rawinstr:Instruction) (ctx:value_context) : IO instruction := 
  do op <- getInstructionOpcode rawinstr,
     tp <- getInstructionType rawinstr >>= extractType,
     match op with
     -- == terminators ==
     -- return
     | 1 := do mv <- getInstructionReturnValue rawinstr,
               (match mv with
                | none := pure instruction.ret_void
                | (some v) := 
                  do tyv <- extractTypedValue v ctx,
                     pure (instruction.ret tyv)
               )

     -- == binary operators ==
     -- add
     | 12 := 
        do uov <- hasNoUnsignedWrap rawinstr,
           sov <- hasNoSignedWrap rawinstr,
           extractBinaryOp rawinstr ctx (instruction.arith (arith_op.add uov sov))
     -- fadd
     | 13 := extractBinaryOp rawinstr ctx (instruction.arith arith_op.fadd)
     -- sub
     | 14 := 
        do uov <- hasNoUnsignedWrap rawinstr,
           sov <- hasNoSignedWrap rawinstr,
           extractBinaryOp rawinstr ctx (instruction.arith (arith_op.sub uov sov))
     -- fsub
     | 15 := extractBinaryOp rawinstr ctx (instruction.arith arith_op.fsub)
     -- mul
     | 16 :=
        do uov <- hasNoUnsignedWrap rawinstr,
           sov <- hasNoSignedWrap rawinstr,
           extractBinaryOp rawinstr ctx (instruction.arith (arith_op.mul uov sov))
     -- fmul 
     | 17 := extractBinaryOp rawinstr ctx (instruction.arith arith_op.fmul)
     -- udiv
     | 18 :=
        do ex <- isExact rawinstr,
           extractBinaryOp rawinstr ctx (instruction.arith (arith_op.udiv ex))
     -- sdiv 
     | 19 :=
        do ex <- isExact rawinstr,
           extractBinaryOp rawinstr ctx (instruction.arith (arith_op.sdiv ex))
     -- fdiv
     | 20 := extractBinaryOp rawinstr ctx (instruction.arith arith_op.fdiv)
     -- urem
     | 21 := extractBinaryOp rawinstr ctx (instruction.arith arith_op.urem)
     -- srem
     | 22 := extractBinaryOp rawinstr ctx (instruction.arith arith_op.srem)
     -- frem
     | 23 := extractBinaryOp rawinstr ctx (instruction.arith arith_op.frem)

     -- icmp
     | 52 := 
          do d <- getCmpInstData rawinstr,
             (match d with
              | none := throw (IO.userError "expected icmp instruction")
              | (some (code, (v1, v2))) :=
                do o1 <- extractTypedValue v1 ctx,
                   o2 <- extractTypedValue v2 ctx,
                   op <- extractICmpOp code,
                   pure (instruction.icmp op o1 o2.value))

     -- select
     | 56 := 
          do d <- getSelectInstData rawinstr,
             (match d with
              | none := throw (IO.userError "expected select instruction")
              | (some (vc, (vt,ve))) :=
                do c <- extractTypedValue vc ctx,
                   t <- extractTypedValue vt ctx,
                   e <- extractTypedValue ve ctx,
                   pure (instruction.select c t e.value)
             )

     | _ := throw (IO.userError ("unimplemented instruction opcode: " ++ (Nat.toDigits 10 op).asString))
.

def extractStmt (rawinstr:Instruction) (ctx:value_context) : IO stmt :=
  do i <- extractInstruction rawinstr ctx,
     pure (stmt.mk (RBMap.find ctx.imap rawinstr) i Array.empty).

def extractStatements (bb:BasicBlock) (ctx:value_context) : IO (Array stmt) :=
  do rawinstrs <- getInstructionArray bb,
     Array.miterate rawinstrs Array.empty (λ_ rawinstr stmts,
       do stmt <- extractStmt rawinstr ctx,
          pure (Array.push stmts stmt)).

def extractBasicBlocks (fn : LLVMFunction) (ctx:value_context) : IO (Array basic_block) :=
  do rawbbs <- getBasicBlockArray fn,
     Array.miterate rawbbs Array.empty (λ_ rawbb bs,
       match RBMap.find ctx.bmap rawbb with
       | none := throw (IO.userError "unknown basic block")
       | (some lab) :=
           do stmts <- extractStatements rawbb ctx,
              pure (Array.push bs (basic_block.mk lab stmts))
       ).

def extractFunction (fn : LLVMFunction) : IO define :=
  do nm <- getFunctionName fn,
     ret <- getReturnType fn >>= extractType,
     (counter, args) <- extractArgs fn,
     (bmap, imap) <- computeNumberings counter fn,

     bbs <- extractBasicBlocks fn (value_context.mk args imap bmap),

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

end llvm.


def main (xs : List String) : IO UInt32 := do

  ctx ← newLLVMContext,
  mb ← newMemoryBufferFromFile xs.head,
  m ← parseBitcodeFile mb ctx,

  getModuleIdentifier m >>= IO.println,

  setModuleIdentifier m "James",
  getModuleIdentifier m >>= IO.println,

  fl <- getFunctionArray m,

  Array.miterate fl () (λ_i f _m,
     do nm <- getFunctionName f,
        dfn <- llvm.extractFunction f,
        IO.println (pp.render (llvm.pp_define dfn))
  ),

  pure 0
  
