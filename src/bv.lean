import init.data.nat
import init.data.nat.div
import init.data.nat.bitwise

structure bv (w : Nat) :=
  ( to_nat : Nat )
  ( prop  : to_nat < 2^w )

namespace bv.
  def less {w:Nat} (x y:bv w) := x.to_nat < y.to_nat.
  instance bvHasLess {w:Nat} : HasLess (bv w) := ⟨bv.less⟩.
  instance decLt {w:Nat} (x y:bv w) : Decidable (x < y) := Nat.decLt x.to_nat y.to_nat.
end bv.

namespace Nat
--local infix `▹`:50 := Eq.trans.

/-
def mod_eq (m:Nat) (x y : Nat) : Prop :=
  ∃(nx ny:Nat), x + m*nx = y + m*ny

def mod_eq_symm (m:Nat) (x y:Nat) :
  mod_eq m x y →
  mod_eq m y x :=

  λ⟨nx, ny, Hxy⟩, ⟨ny, nx, Eq.symm Hxy ⟩.

def mod_eq_refl (m:Nat) (x y:Nat) :
  x = y →
  mod_eq m x y :=

  λ H, ⟨ 0, 0, H ⟩.


def mod_eq_trans (m:Nat) (x y z:Nat) :
  mod_eq m x y →
  mod_eq m y z →
  mod_eq m x z  :=

  λ⟨nx, ny, Hxy⟩ ⟨ny', nz, Hyz⟩,
    ⟨ nx + ny', ny + nz,
       (congrArg _ (Nat.leftDistrib _ _ _) ▹ (Nat.addAssoc _ _ _).symm) ▹
       (congr (congrArg _ Hxy) rfl) ▹ Nat.addAssoc _ _ _ ▹
       Eq.symm (
       (congrArg _ (Nat.leftDistrib _ _ _) ▹ congrArg _ (Nat.addComm _ _) ▹ (Nat.addAssoc _ _ _).symm) ▹
       congr (congrArg _ Hyz.symm) rfl ▹ Nat.addAssoc _ _ _ ▹
       congrArg _ (Nat.addComm _ _))
    ⟩.

def eq_le {x y:Nat} (H:x = y) : x ≤ y :=
  H ▸ Nat.leRefl x.

def sub_cancel (x:Nat) : ∀m, (x + m) - m = x :=
  @Nat.rec (λm, (x+m) - m = x) rfl (λm (H:(x+m)-m = x),
     have H' : (succ (x+m) - succ m) = (x+m) - m := Nat.succSubSuccEqSub (x+m) m,
     Eq.trans H' H).

def sub_cancel2 : ∀(x m:Nat), m ≤ x → (x-m) + m = x :=
  @Nat.rec (λ x, ∀m, m ≤ x → (x-m) + m = x)
    (λ m, Nat.casesOn m (λ _, rfl) (λn H, False.elim (Nat.notLtZero _ H)))
    (λ x Hind m, Nat.casesOn m (λ _, rfl) (λ n H,
      have Hnx : n ≤ x := leOfSuccLeSucc H,
      have Hsub : (x - n) + n = x := Hind _ Hnx,
      congrArg succ (congr (congrArg Nat.add (Nat.succSubSuccEqSub _ _)) rfl ▹ Hsub)
      ))
.

def euclidian_div (m x:Nat) : x = x%m + m*(x/m) :=

  Nat.div.inductionOn x m
    (λ a b H1 H2,
      have Hdiv  : a/b = (a-b)/b + 1 := Nat.divDef a b ▹ ifPos H1,
      have Hdiv' : b*(a/b) = b*((a-b)/b + 1) := congrArg _ Hdiv,
      have Hmod : a%b = (a-b)%b     := Nat.modDef a b ▹ ifPos H1,
      have Ha   : a = (a-b) + b     := (sub_cancel2 a b H1.right).symm,
      Ha ▹ congr (congrArg _ H2) rfl ▹ Nat.addAssoc _ _ _ ▹
      congr (congrArg _ Hmod.symm) Hdiv'.symm
    )
    (λ a b H,
     have Hdiv : a/b = 0 := Nat.divDef a b ▹ ifNeg H,
     have Hdiv' : b*(a/b) = 0 := congrArg _ Hdiv ▹ rfl,
     have Hmod  : a%b = a := Nat.modDef a b ▹ ifNeg H,
     Hmod.symm ▹ (Nat.addZero (a%b)).symm ▹ congrArg _ Hdiv'.symm)
.

def mod_eq_mod (m x:Nat) : mod_eq m x (x%m) :=
  ⟨ 0, x/m, euclidian_div m x ⟩
.

def mod_reduce (m x:Nat) : ∀n, (x + m*n) % m = x % m :=

  @Nat.rec (λn,(x + m*n) % m = x % m) rfl (λn H,
    have Hm : m ≤ x + (m*n + m) :=
      Nat.leTrans
        (eq_le (Nat.zeroAdd m).symm)
        (Nat.addAssoc x (m*n) m ▸ Nat.addLeAddRight (Nat.zeroLe (x + m*n)) m),
    have Hred : (x + m*succ n)%m = (x + m*succ n - m)%m := Nat.modEqSubMod Hm,
    have Hsucc_sub : x+(m*n + m) - m = x+m*n := Nat.addAssoc x (m*n) m ▸ sub_cancel (x+m*n) m,
    have H': (x + m*succ n)%m = (x + m*n)%m := Hsucc_sub ▸ Hred,
    H ▸ H')
.


def rearrange1 (a b c d : Nat) :
  (a+b)+(c+d) = a + c + (b + d) :=

  Nat.addAssoc a b (c+d) ▹
  congr rfl
    ((Nat.addAssoc b c d).symm ▹ congr (congrArg _ (Nat.addComm b c)) rfl ▹
     (Nat.addAssoc c b d)
    ) ▹
  (Nat.addAssoc a c (b+d)).symm
.

def mod_homomorphism_add (m:Nat) (a b c d:Nat) :
  mod_eq m a c →
  mod_eq m b d →
  mod_eq m (a + b) (c + d) :=

 λ⟨ na, nc, Hac ⟩, λ⟨ nb, nd, Hbd ⟩,
   ⟨ na + nb, nc + nd ,
      have H1 : (a + m*na)+(b + m *nb) = (c + m*nc)+(d + m*nd) := congr (congrArg Nat.add Hac) Hbd,
      have H2 : a + b + (m * na + m * nb) = c + d + (m*nc + m*nd) :=
        (rearrange1 a b (m*na) (m*nb)) ▹ H1 ▹ (rearrange1 c d (m*nc) (m*nd)).symm,
      (Nat.leftDistrib m nc nd).symm ▸ (Nat.leftDistrib m na nb).symm ▸ H2
   ⟩.


def rearrange2 (a b c d m:Nat) :
  (a+m*b)*(c+m*d) = a*c + m*(a*d + c*b + b*d*m) :=

  have H1 : m * (a * d) = a * (m * d) :=
     (Nat.mulAssoc _ _ _).symm ▹ congr (congrArg _ (Nat.mulComm _ _)) rfl ▹ Nat.mulAssoc _ _ _,
  have H2 : m * (c * b) = m * b * c :=
     congrArg _ (Nat.mulComm _ _) ▹ (Nat.mulAssoc _ _ _).symm,
  have H3 : m * (b * d * m) = m * b * (m * d) := Eq.symm (
     Nat.mulAssoc _ _ _ ▹ congrArg _ ( congrArg _ (Nat.mulComm _ _) ▹ (Nat.mulAssoc _ _ _).symm)),

  Nat.leftDistrib (a+m*b) c (m*d) ▹
  congr (congrArg Nat.add (Nat.rightDistrib _ _ _)) rfl ▹
  Nat.addAssoc _ _ _ ▹
  congrArg _ (
    (congrArg _ (Nat.rightDistrib _ _ _)) ▹
    (Nat.addAssoc _ _ _).symm ▹
    (congr (congrArg _ (Nat.addComm _ _)) rfl) ▹
    (Eq.symm (Nat.leftDistrib _ _ _ ▹
              congr (congrArg _ (Nat.leftDistrib _ _ _ ▹ congr (congrArg _ H1) H2)) H3))
   ).

def mod_homomorphism_mul (m:Nat) (a b c d:Nat) :
  mod_eq m a c →
  mod_eq m b d →
  mod_eq m (a * b) (c * d) :=

 λ⟨ na, nc, Hac ⟩, λ⟨ nb, nd, Hbd ⟩,
   ⟨ a*nb + b*na + na*nb*m, c*nd + d*nc + nc*nd*m,
      have H1 : (a + m*na)*(b + m *nb) = (c + m*nc)*(d + m*nd) := congr (congrArg Nat.mul Hac) Hbd,
      (rearrange2 a na b nb m).symm ▹ H1 ▹ rearrange2 c nc d nd m
   ⟩.

def mod_eq_eq (m:Nat) (x y:Nat) :
  mod_eq m x y →
  x%m = y%m :=

 λ⟨ nx, ny, Hxy ⟩,
   have Hxy' : (x + m * nx)%m = (y + m*ny)%m := congr (congrArg Nat.mod Hxy) rfl,
   mod_reduce m y ny ▸ mod_reduce m x nx ▸ Hxy'.

def mod_eq_eq' (m:Nat) (x y:Nat) :
  x%m = y%m →
  mod_eq m x y :=

  λH,

  have x+y = y+x,
    from Nat.addComm x y,
  have x+(x%m + m*(y/m)) = y + (x%m + m*(x/m)),
    from Nat.euclidian_div m x ▸ H.symm ▸ Nat.euclidian_div m y ▸ this,
  have x%m + (x+m*(y/m)) = x%m + (y + m*(x/m)),
    from (Nat.addAssoc _ _ _).symm ▹ congr (congrArg _ (Nat.addComm _ _)) rfl ▹ Nat.addAssoc _ _ _ ▹ this ▹
         (Nat.addAssoc _ _ _).symm ▹ congr (congrArg _ (Nat.addComm _ _)) rfl ▹ Nat.addAssoc _ _ _,
  ⟨ y/m , x/m, Nat.addLeftCancel this⟩
.
-/

end Nat

namespace bv
/-
local infix `▹`:50 := Eq.trans.
-/

protected def from_nat (w:Nat) (val:Nat) : bv w :=
  ⟨val % 2^w, Nat.modLt val (Nat.posPowOfPos w rfl) ⟩.

protected def from_int (w:Nat) : Int → bv w
| Int.ofNat n   => bv.from_nat w n
| Int.negSucc n => let n' := (n % 2^(w-1))+1; bv.from_nat w (2^w - n')
.

protected def to_int {w} (x:bv w) : Int :=
  if x.to_nat < 2^(w-1) then
    Int.ofNat x.to_nat
  else
    Int.ofNat x.to_nat - Int.ofNat (2^w)
.

def bv_ext {w:Nat} : ∀{x y:bv w}, x.to_nat = y.to_nat → x = y
| ⟨xv, xp⟩, ⟨_,yp⟩, rfl => rfl
.

def add {w:Nat} (x y : bv w) : bv w :=
  bv.from_nat w (x.to_nat + y.to_nat).

def sub {w:Nat} (x y : bv w) : bv w :=
  bv.from_nat w (x.to_nat + (2^w - y.to_nat)).

def negate {w:Nat} (x : bv w) : bv w :=
  bv.from_nat w (2^w - x.to_nat).

def mul {w:Nat} (x y : bv w) : bv w :=
  bv.from_nat w (x.to_nat * y.to_nat).

def bitwise_and {w:Nat} (x y: bv w) : bv w :=
  bv.from_nat w (Nat.land x.to_nat y.to_nat).

def bitwise_or {w:Nat} (x y: bv w) : bv w :=
  bv.from_nat w (Nat.lor x.to_nat y.to_nat).

-- TODO, define/bind to efficent versions of these bitwise operations
def bitwise_xor {w:Nat} (x y:bv w) : bv w :=
  bv.from_nat w (Nat.bitwise xor x.to_nat y.to_nat).

def shl {w:Nat} (x y: bv w) : bv w :=
  bv.from_nat w (x.to_nat * (2 ^ y.to_nat)).

def lshr {w:Nat} (x y:bv w) : bv w :=
  bv.from_nat w (x.to_nat / (2 ^ y.to_nat)).

def ashr {w:Nat} (x y:bv w) : bv w :=
  bv.from_int w (x.to_int / Int.ofNat (2 ^ y.to_nat)).


/-
def bv_mod_eq (w:Nat) (x y:Nat) : Nat.mod_eq (2^w) x y → bv.from_nat w x = bv.from_nat w y :=
  bv_ext ∘ Nat.mod_eq_eq (2^w) x y.

def add_assoc (w:Nat) (x y z:bv w) :
  bv.add x (bv.add y z) = bv.add (bv.add x y) z :=

  have H1 : Nat.mod_eq (2^w) (x.to_nat + (bv.add y z).to_nat) (x.to_nat + (y.to_nat + z.to_nat)) :=
    Nat.mod_homomorphism_add (2^w) _ _ _ _ (Nat.mod_eq_refl _ _ _ rfl) (Nat.mod_eq_symm _ _ _ (Nat.mod_eq_mod (2^w) _)),
  have H2 : Nat.mod_eq (2^w) ((bv.add x y).to_nat + z.to_nat) ((x.to_nat + y.to_nat) + z.to_nat) :=
    Nat.mod_homomorphism_add (2^w) _ _ _ _ (Nat.mod_eq_symm _ _ _ (Nat.mod_eq_mod _ _)) (Nat.mod_eq_refl _ _ _ rfl),

  bv_mod_eq w _ _
    (Nat.mod_eq_trans _ _ _ _
      (Nat.mod_eq_trans _ _ _ _ H1
      (Nat.mod_eq_refl _ _ _ (Nat.addAssoc _ _ _).symm)) (Nat.mod_eq_symm _ _ _ H2))
.

def sub_add_negate (w:Nat) (x y:bv w) :
  bv.add x (bv.negate y) = bv.sub x y :=

  bv_mod_eq w _ _
      (Nat.mod_homomorphism_add _ _ _ _ _
        (Nat.mod_eq_refl _ _ _ rfl)
        (Nat.mod_eq_symm _ _ _ (Nat.mod_eq_mod _ _))).

def negate_inverse (w:Nat) (x:bv w) :
  bv.add x (bv.negate x) = bv.from_nat w 0 :=

  have H1 : Nat.mod_eq (2^w) (x.to_nat + (2^w - x.to_nat)%2^w) (x.to_nat + (2^w - x.to_nat)) :=
    Nat.mod_homomorphism_add _ _ _ _ _ (Nat.mod_eq_refl _ _ _ rfl) (Nat.mod_eq_symm _ _ _ (Nat.mod_eq_mod _ _)),
  have H2 : Nat.mod_eq (2^w) (x.to_nat + (2^w - x.to_nat)) (2^w) := Nat.mod_eq_refl _ _ _
    ( Nat.addComm _ _ ▹ Nat.sub_cancel2 _ _ (Nat.leOfLt x.prop)),
  have H3 : Nat.mod_eq (2^w) (2^w) 0 :=
    ⟨ 0, 1, (Nat.zeroAdd (2^w)).symm ▹ congrArg _ (Nat.mulOne _).symm⟩,
  have H4 : Nat.mod_eq (2^w) (x.to_nat + (2^w - x.to_nat)%2^w) 0 :=
    Nat.mod_eq_trans (2^w) _ _ _  (Nat.mod_eq_trans (2^w) _ _ (2^w) H1 H2) H3,

  bv_mod_eq w _ _ H4.
.

-/

end bv.
