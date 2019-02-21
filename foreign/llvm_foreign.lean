-- This file ccontains
import .foreign

namespace llvm

namespace ffi

open foreign
open foreign.c


noncomputable
def llvmbool := cint

--foreign import "LLVMDisposeMessage"
constant disposeMessage : cstring → io unit

inductive opague_memory_buffer

def memory_buffer_ref := ptr opague_memory_buffer

--foreign import "LLVMCreateMemoryBufferWithContentsOfFile"
constant
  createMemoryBufferWithContentsOfFile : cstring
                                       → ptr memory_buffer_ref
                                       → ptr cstring
                                       → io llvmbool

end ffi
end llvm
