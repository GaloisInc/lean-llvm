import tactic.linarith

namespace sized

def map {a b:Type} [has_sizeof a] (sz:ℕ) (f : Πx:a, sizeof x < sz → b) : Πxs:list a, (sizeof xs <= sz) → list b
| [] _      := []
| (x::xs) H :=
   have Hx  : sizeof x  <  sz, by { unfold sizeof has_sizeof.sizeof list.sizeof at *, linarith },
   have Hxs : sizeof xs <= sz, by { unfold sizeof has_sizeof.sizeof list.sizeof at *, linarith },
   f x Hx :: map xs Hxs
.

@[reducible]
def map_over {a b:Type} [has_sizeof a] (xs:list a) (f : Πx:a, sizeof x < sizeof xs → b) : list b :=
  map (sizeof xs) f xs (nat.less_than_or_equal.refl _).

@[reducible]
def psum_size {A B:Type} (f:A → ℕ) (g:B → ℕ) : psum A B → ℕ
| (psum.inl x) := f x
| (psum.inr y) := g y
.

@[reducible]
def psum3_has_wf {A B C:Type} [has_sizeof A] [has_sizeof B] [has_sizeof C] : has_well_founded (psum A (psum B C)) :=
  ⟨ measure (psum_size sizeof (psum_size sizeof sizeof))
  , measure_wf _
  ⟩.

@[reducible]
def psum4_has_wf {A B C D:Type} [has_sizeof A] [has_sizeof B] [has_sizeof C] [has_sizeof D]: has_well_founded (psum A (psum B (psum C D))) :=
  ⟨ measure (psum_size sizeof (psum_size sizeof (psum_size sizeof sizeof)))
  , measure_wf _
  ⟩.


end sized
