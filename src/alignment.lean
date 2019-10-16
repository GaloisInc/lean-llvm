
import init.data.rbmap


namespace RBNode
universes u v
variables {α : Type u} {β : α → Type v}
section

variable (lt : α → α → Bool)

@[specialize] def upperBound : RBNode α β → α → Option (Sigma β) → Option (Sigma β)
| leaf, x, ub             => ub
| node _ a ky vy b, x, ub =>
   if lt x ky then upperBound a x (some ⟨ky, vy⟩)
   else if lt ky x then upperBound b x ub
   else some ⟨ky, vy⟩
end

end RBNode

namespace RBMap
universes u v
variables {α : Type u} {β : Type v} {lt : α → α → Bool}

/- (upperBound k) retrieves the kv pair of the smallest key larger than or equal to `k`,
   if it exists -/
@[inline] def upperBound : RBMap α β lt → α → Option (Sigma (fun (k : α) => β))
| ⟨t, _⟩, x => t.upperBound lt x none

end RBMap.

structure bytes := ( val : Nat ).

def toBytes (x:Nat) : bytes :=
  bytes.mk ((x+7)/8).

namespace bytes.
def asString (x:bytes) : String := (Nat.toDigits 10 x.val).asString

def toBits (x:bytes) : Nat := 8 * x.val.

def mul (x:bytes) (y:Nat) : bytes :=
  bytes.mk (x.val * y).

def add (x:bytes) (y:bytes) : bytes :=
  bytes.mk (x.val + y.val).

def sub (x:bytes) (y:bytes) : bytes :=
  bytes.mk (x.val - y.val).

instance inhab : Inhabited bytes := ⟨bytes.mk 0⟩

end bytes.

namespace llvm

-- An alignemnt represents a number of bytes that must be a power of 2,
-- and is represented via its exponent
structure alignment :=
  (exponent : Nat ).

-- 1-byte alignment, which is the minimum possible
def noAlignment := alignment.mk 0.

def maxAlignment (x y:alignment) : alignment :=
  alignment.mk (Nat.max x.exponent y.exponent).

instance alignment.inh : Inhabited alignment := ⟨noAlignment⟩.

def nextMultiple (x:Nat) (n:Nat) : Nat := ((x + n - 1)/n) * n

def prevMultiple (x:Nat) (n:Nat) : Nat := (x/n) * n

def padToAlignment (x:bytes) (al:alignment) : bytes :=
  bytes.mk (nextMultiple x.val (2^al.exponent)).

def padDownToAlignment (x:bytes) (al:alignment) : bytes :=
  bytes.mk (prevMultiple x.val (2^al.exponent)).

partial def lg2aux : Nat → Nat → Nat
| r, 0 => r
| r, n => lg2aux (r+1) (n/2)

def toAlignment (x:Nat) : Option alignment :=
  let l := lg2aux 0 (x/2);
  if 2^l = x then some (alignment.mk l) else none.

def fromAlignment (x:alignment) : Nat := 2^x.exponent.


@[reducible]
def alignInfo := @RBMap Nat alignment (λx y => decide (x < y)).


-- Get alignment for the integer type of the specified bitwidth,
-- using LLVM's rules for integer types: "If no match is found, and
-- the type sought is an integer type, then the smallest integer type
-- that is larger than the bitwidth of the sought type is used. If
-- none of the specifications are larger than the bitwidth then the
-- largest integer type is used."
-- <http://llvm.org/docs/LangRef.html#langref-datalayout>
@[reducible]
def computeIntegerAlignment (ai:alignInfo) (k:Nat) : alignment :=
  match ai.upperBound k with
  | some ⟨_, a⟩ => a
  | none =>
    match ai.max with
    | some ⟨_, a⟩ => a
    | none => noAlignment
.

-- | Get alignment for a vector type of the specified bitwidth, using
-- LLVM's rules for vector types: "If no match is found, and the type
-- sought is a vector type, then the largest vector type that is
-- smaller than the sought vector type will be used as a fall back."
-- <http://llvm.org/docs/LangRef.html#langref-datalayout>
@[reducible]
def computeVectorAlignment (ai:alignInfo) (k:Nat) : alignment :=
  match ai.lowerBound k with
  | some ⟨_, a⟩ => a
  | none => noAlignment
.

end llvm
