import init.data.array
import init.data.int
import init.data.rbmap

import .ast
import .pp
import .data_layout
import .llvm_ffi


namespace llvm.
namespace output.


@[reducible]
def symMap := RBMap symbol LLVMValue (λx y => decide (x < y))

@[reducible]
def blockMap := RBMap block_label LLVMValue (λx y => decide (x.label < y.label))

@[reducible]
def valueMap := RBMap ident LLVMValue (λx y => decide (x < y))

@[reducible]
def typeMap := RBMap String LLVMType (λx y => decide (x < y))

structure value_context :=
  ( symbol_map : symMap )
  ( block_map  : blockMap )
  ( value_map  : valueMap )
  ( type_map   : typeMap )


end output.
end llvm.
