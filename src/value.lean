import init.data.rbmap

import .ast
import .bv
import .pp
import .type_context


namespace llvm.
namespace sim.

inductive value : Type
| bv       (w : Nat) : bv w → value
| vec    : mem_type → Array value → value
| array  : mem_type → Array value → value
| struct : Array (fieldInfo value) → value
.


namespace value.

partial def pretty : value → pp.doc
| bv w x => pp.text x.asString
| vec _mt xs   => pp.angles (pp.commas (xs.toList.map pretty))
| array _mt xs => pp.brackets (pp.commas (xs.toList.map pretty))
| struct fs => pp.braces (pp.commas (fs.toList.map (λfi => pretty fi.value)))

def asString (v:value) : String := pp.render (pretty v)

end value.


@[reducible]
def memMap := @RBMap (bv 64) (bv 8) (λx y => decide (x < y)).

@[reducible]
def regMap := @RBMap ident value (λx y => decide (x < y)).

end sim.
end llvm.
