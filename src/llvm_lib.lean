import init.data.array

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
constant BasicBlock := Unit

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

@[extern 2 cpp "lean_llvm::getBasicBlockArray"]
def getBasicBlockArray : @& LLVMFunction -> IO (Array BasicBlock) := default _

@[extern 2 cpp "lean_llvm::getBBName"]
def getBBName : @& BasicBlock -> IO (Option String) := default _


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
        IO.println ("fun : " ++ nm),
        bbs <- getBasicBlockArray f,
        Array.miterate bbs () (λbb_idx bb _m,
          do bbnm <- getBBName bb,
             (match bbnm with
              | none := IO.println( "anonymous bb: " ++ (Nat.toDigits 10 bb_idx.val).toString )
              | (some x) :=  IO.println( "bb: " ++ x)
             )
        )
  ),

  pure 0
