import Std.Data.RBMap

import Galois.Data.Bitvec

import LeanLLVM.AST
import LeanLLVM.PP
import LeanLLVM.TypeContext

open Std (RBMap)

namespace LLVM
namespace Sim

inductive Value : Type
| bv {w : Nat} (x:bitvec w) : Value
| vec (eltTp:mem_type) (x:Array Value) : Value
| array (eltTp:mem_type) (values:Array Value) : Value
| struct (fields:Array (fieldInfo Value)) : Value

namespace Value

partial def pretty : Value → Doc
| bv x => Doc.text x.pp_hex
| vec _mt xs   => Doc.angles (Doc.commas (xs.toList.map pretty))
| array _mt xs => Doc.brackets (Doc.commas (xs.toList.map pretty))
| struct fs => Doc.braces (Doc.commas (fs.toList.map (λfi => pretty fi.value)))

def asString (v:Value) : String := Doc.render (pretty v)

end Value

@[reducible]
def memMap := RBMap (bitvec 64) (bitvec 8) Ord.compare

@[reducible]
def regMap := RBMap Ident Value Ord.compare

end Sim
end LLVM
