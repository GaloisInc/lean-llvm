import .llvm_ffi

--@[extern 3 cpp "lean_llvm::compileCFile"]
--def compileCFile : LLVMContext → @&String → IO Module := default _

--@[extern 3 cpp "lean_llvm::compileCPPFile"]
--def compileCPPFile : LLVMContext → @&String → IO Module := default _

------------------------------------------------------------------------
-- CompilerSession

@[extern 3 "lean_llvm_invokeClang"]
def invokeClang : LLVMContext → @&(Array String) → IO Module := default _

constant CompilerSession := Unit

/-- This constructs a compiler session and frees it when done. -/
@[extern 2 "lean_llvm_newCompilerSession"]
constant newCompilerSession : Triple → IO CompilerSession := default _

@[extern 3 "lean_llvm_addFromClangCompile"]
constant addFromClang : @&CompilerSession → @&(Array String) → IO Unit := default _

@[extern 4 "lean_llvm_lookupFn"]
constant lookupFn : @&CompilerSession → @&String → ∀(t:@&Type), IO t := default _
