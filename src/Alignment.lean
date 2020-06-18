
import Init.Data.RBMap


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

end RBMap

namespace LLVM

-- An alignment represents a number of bytes that must be a power of 2,
-- and is represented via its exponent
structure Alignment := (exponent : Nat)

-- 1-byte alignment, which is the minimum possible
def unaligned : Alignment := ⟨0⟩

-- 2-byte alignment
def align2 : Alignment := ⟨1⟩
-- 4-byte alignment
def align4 : Alignment := ⟨2⟩
-- 8-byte alignment
def align8 : Alignment := ⟨3⟩
-- 16-byte alignment
def align16 : Alignment := ⟨4⟩

def maxAlignment (x y: Alignment) : Alignment := ⟨Nat.max x.exponent y.exponent⟩

instance alignment.inh : Inhabited Alignment := ⟨unaligned⟩

partial def lg2aux : Nat → Nat → Nat
| r, 0 => r
| r, n => lg2aux (r+1) (n/2)

def toAlignment (x:Nat) : Option Alignment :=
  let l := lg2aux 0 (x/2);
  if 2^l = x then some ⟨l⟩ else none

-- @padToAlignment x a@ returns the smallest value aligned with @a@ not less than @x@.
def padToAlignment (x:Nat) (a:Alignment) := 
  let m : Nat := 2^a.exponent;
  (x + m - 1)/m * m

-- @padDownToAlignment x a@ returns the largest value aligned with @a@ that is not larger than @x@.
def padDownToAlignment (x:Nat) (a:Alignment) : Nat :=
  let m : Nat := 2^a.exponent; x/m * m

def AlignInfo := RBMap Nat Alignment (λx y => decide (x < y))

-- Get alignment for the integer type of the specified bitwidth,
-- using LLVM's rules for integer types: "If no match is found, and
-- the type sought is an integer type, then the smallest integer type
-- that is larger than the bitwidth of the sought type is used. If
-- none of the specifications are larger than the bitwidth then the
-- largest integer type is used."
-- <http://llvm.org/docs/LangRef.html#langref-datalayout>
def computeIntegerAlignment (ai:AlignInfo) (k:Nat) : Alignment :=
  match ai.upperBound k with
  | some ⟨_, a⟩ => a
  | none =>
    match ai.max with
    | some ⟨_, a⟩ => a
    | none => unaligned

-- | Get alignment for a vector type of the specified bitwidth, using
-- LLVM's rules for vector types: "If no match is found, and the type
-- sought is a vector type, then the largest vector type that is
-- smaller than the sought vector type will be used as a fall back."
-- <http://llvm.org/docs/LangRef.html#langref-datalayout>
def computeVectorAlignment (ai:AlignInfo) (k:Nat) : Alignment :=
  match ai.lowerBound k with
  | some ⟨_, a⟩ => a
  | none => unaligned

end LLVM
