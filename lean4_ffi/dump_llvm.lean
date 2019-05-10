
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

/-- This constructs a LLVM Context and frees it when done. -/
@[extern 1 cpp "lean_llvm::newLLVMContext"]
constant newLLVMContext : IO LLVMContext := default _

constant MemoryBuffer := Unit

@[extern 2 cpp "lean_llvm::newMemoryBufferFromFile"]
def newMemoryBufferFromFile : String → IO MemoryBuffer := default _


constant Module := Unit

@[extern 3 cpp "lean_llvm::parseBitcodeFile"]
def parseBitcodeFile : MemoryBuffer → LLVMContext → IO Module := default _

@[extern 2 cpp "lean_llvm::getModuleIdentifier"]
def getModuleIdentifier : Module → IO String := default _

@[extern 3 cpp "lean_llvm::setModuleIdentifier"]
def setModuleIdentifier : Module → String → IO Unit := default _


def main (xs : List String) : IO UInt32 := do

  ctx ← newLLVMContext,
  mb ← newMemoryBufferFromFile xs.head,
  m ← parseBitcodeFile mb ctx,

  getModuleIdentifier m >>= IO.println,

  setModuleIdentifier m "Bob",
  getModuleIdentifier m >>= IO.println,
  pure 0
