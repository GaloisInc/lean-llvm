import .llvm_ffi

@[extern 3 cpp "lean_llvm::compileCFile"]
def compileCFile : LLVMContext → @&String → IO Module := default _

@[extern 3 cpp "lean_llvm::compileCPPFile"]
def compileCPPFile : LLVMContext → @&String → IO Module := default _
