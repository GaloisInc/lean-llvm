import init.data.rbmap

import .ast
import .type_context

namespace llvm.
namespace simulator.

inductive value : Type
| bv     : Π(width : ℕ), ℕ → value 
| ptr    : sym_type → ℕ → value
| vec    : mem_type → List value → value
| array  : mem_type → List value → value
| struct : Π(packed:Bool), List (mem_type × value) → value
| undef  : mem_type → value
.

inductive effect : Type
| mem_read 


def value_type : value → mem_type
| (value.bv w _)               := mem_type.int w
| (value.ptr symtp _)          := mem_type.ptr symtp
| (value.vec tp xs)            := mem_type.vector xs.length tp
| (value.array tp xs)          := mem_type.array xs.length tp
| (value.struct Bool.false fs) := mem_type.struct (List.map Prod.fst fs)
| (value.struct Bool.true fs)  := mem_type.packed_struct (List.map Prod.fst fs)
.

@[reducible]
def identEq (a b:ident) := @toBool _ (String.decLt a.ident b.ident).

@[reducible]
def env := @RBMap ident value identEq.

def toUnsigned (w:ℕ) : Int → ℕ
| (Int.ofNat n)   := n % pow 2 w
| (Int.negSucc n) := pow 2 w - (Nat.succ n % pow 2 w)
.

partial def evaluate (ρ:env) : mem_type → llvm.value → Option simulator.value
| (mem_type.int w) (llvm.value.integer x) := some (value.bv w (toUnsigned w x))
| (mem_type.int 1) (llvm.value.bool b) := 
    (match b with
     | true  := some (value.bv 1 1)
     | false := some (value.bv 1 0))
| _t (llvm.value.ident i)              := RBMap.find ρ i
| (mem_type.int w) llvm.value.null     := some (value.bv w 0)
| (mem_type.ptr symtp) llvm.value.null := some (value.ptr symtp 0)
| (mem_type.array n tp) (llvm.value.array _ xs) :=
    (match decEq n xs.length with
     | Decidable.isTrue _  := value.array tp <$> List.mmap (evaluate tp) xs
     | Decidable.isFalse _ := none)
| (mem_type.vector n tp) (llvm.value.vector _ xs) :=
    (match decEq n xs.length with
     | Decidable.isTrue _  := value.vec tp <$> List.mmap (evaluate tp) xs
     | Decidable.isFalse _ := none)
| (mem_type.struct tps) (llvm.value.struct vs) :=
    (match decEq tps.length vs.length with
     | Decidable.isTrue _ := value.struct false <$>
         List.mmap
         (λx, do z <- evaluate (Prod.fst x) (typed.value (Prod.snd x)),
                 pure (Prod.fst x, z))
         (List.zip tps vs)
     | Decidable.isFalse _ := none)

| (mem_type.packed_struct tps) (llvm.value.packed_struct vs) :=
    (match decEq tps.length vs.length with
     | Decidable.isTrue _ := value.struct true <$>
         List.mmap
         (λx, do z <- evaluate (Prod.fst x) (typed.value (Prod.snd x)),
                 pure (Prod.fst x, z))
         (List.zip tps vs)
     | Decidable.isFalse _ := none)

| tp llvm.value.undef := value.undef tp



-- | _t (llvm.value.const_expr cexp)      := none -- FIXME!
-- | _t (llvm.value.symbol sym)           := none -- FIXME!
| _t _val := none
.


end simulator.
end llvm.
