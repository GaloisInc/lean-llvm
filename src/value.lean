import init.data.rbmap

import .ast
import .bv
import .type_context

namespace llvm.
namespace sim.

inductive value : Type
| bv       (w : Nat) : bv w → value
| vec    : mem_type → Array value → value
| array  : mem_type → Array value → value
| struct : Array (fieldInfo value) → value
.

@[reducible]
def memMap := @RBMap (bv 64) (bv 8) (λx y => decide (x < y)).

@[reducible]
def regMap := @RBMap ident value (λx y => decide (x < y)).

end sim.
end llvm.
