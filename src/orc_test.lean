import .llvm_ffi
import .clang_ffi

def main (xs : List String) : IO UInt32 := do

  ctx ← newLLVMContext;
  m ← compileCPPFile ctx xs.head;
  pure 0
