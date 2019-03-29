import data.list
import data.rbmap
import tactic.linarith

import .ast
import .sized
  

lemma rbmap_insert_lookup_eq {α:Type} {β:Type} {lt:α → α → Prop} [Hdec:decidable_rel lt]
  (m:rbmap α β lt)
  (k:α) (x:β)
  : forall a, cmp_using lt a k = ordering.eq → rbmap.find (rbmap.insert m k x) a = some x 
:= sorry

lemma rbmap_insert_lookup_neq {α:Type} {β:Type} {lt:α → α → Prop} [Hdec:decidable_rel lt]
  (m:rbmap α β lt)
  (k:α) (x:β)
  : forall a, cmp_using lt a k ≠ ordering.eq → rbmap.find (rbmap.insert m k x) a = rbmap.find m a
:= sorry


namespace llvm.


meta def llvm_type_tac :=
  `[unfold has_well_founded.r measure inv_image sizeof has_sizeof.sizeof
      llvm_type.sizeof
      at *,
    try { linarith }
   ].

@[simp]
def mentions : llvm_type → list ident
| (llvm_type.prim_type _) := []
| (llvm_type.alias i) := [i]
| (llvm_type.array _n tp) := mentions tp
| (llvm_type.fun_ty ret args _va) := mentions ret ++ (list.join (sized.map_over args (λ x H, mentions x)))
| (llvm_type.ptr_to _) := [] -- NB pointer types are explicitly excluded
| (llvm_type.struct fs) := list.join (sized.map_over fs (λ x H, mentions x))
| (llvm_type.packed_struct fs) := list.join (sized.map_over fs (λ x H, mentions x))
| (llvm_type.vector _n tp) := mentions tp
| (llvm_type.opaque) := []

using_well_founded ⟨λ _ _, `[exact ⟨measure sizeof, measure_wf _⟩] , llvm_type_tac⟩
.

@[reducible,simp]
def alias_rel (am:strmap llvm_type) (x y:ident) : Prop :=
  ∃tp, am.find y.ident = some tp /\ x ∈ mentions tp.

instance ident_eq_dec : decidable_rel (@eq ident) :=
begin
  unfold decidable_rel, intros a b, cases a, cases b, simp, apply_instance
end

@[reducible]
def alias_map := { am:strmap llvm_type // (forall a, acc (alias_rel am) a) }.

namespace alias_map.

def all_mem_dec {α:Type} (p:α → Prop) (l:list α) :
  (∀x, x ∈ l → decidable (p x)) →
  decidable (∀x, x ∈ l → p x) :=
begin
  induction l,
  case list.nil {
    intros, unfold has_mem.mem list.mem,
    right; intros, trivial,
  },
  case list.cons {
    intros, unfold has_mem.mem list.mem, intros,
    cases (a l_hd (or.inl rfl)),
    { left, intro, apply h, apply a_1, simp, },
    { have Hsub : (Π (x : α), x ∈ l_tl → decidable (p x)),
      { intros; apply a, apply or.inr, assumption },
      cases (l_ih Hsub),
      { left, intro, apply h_1, intros, apply a_1, apply or.inr, assumption },
      { right, intros, cases a_1,
        { subst x; assumption },
        { apply h_1; assumption }
      }
    }
  }
end

def ex_mem_dec {α:Type} (p:α → Prop) (l:list α) :
  (∀x, x ∈ l → decidable (p x)) →
  decidable (∃x, x ∈ l ∧ p x) :=
begin
  induction l,
  case list.nil {
    intros, unfold has_mem.mem list.mem,
    left, intro H, cases H, cases H_h, trivial
  },
  case list.cons {
    intros, unfold has_mem.mem list.mem, intros,
    cases (a l_hd (or.inl rfl)),
    { have Hsub : (Π (x : α), x ∈ l_tl → decidable (p x)),
      { intros; apply a, apply or.inr, assumption },
      cases (l_ih Hsub),
      { left, intro H, cases H, cases H_h, cases H_h_left,
        { apply h; cc },
        { apply h_1, existsi H_w, cc }
      },
      { right, cases h_1, existsi h_1_w, cases h_1_h, split,
        apply or.inr, assumption, assumption,
      }
    },
    { right, existsi l_hd, split; try {assumption}, left, refl,
    }
  }
end.


def reachable_dec 
  (am:strmap llvm_type) 
  : forall x y (Hacc : acc (alias_rel am) y), decidable (tc (alias_rel am) x y) :=
begin
  intros x y Hacc, apply Hacc.rec_on, clear Hacc y, intros y _ IH,
  destruct (am.find y.ident),
  { intros Hy, left, intro Htc, revert Hy, clear IH,
    induction Htc,
    { intros, cases Htc_a_1, cc, },
    { intros, cc }
  },
  intros tp Htp,
  have H : decidable (∃i, i ∈ mentions tp ∧ (i = x ∨ tc (alias_rel am) x i)),
  { apply ex_mem_dec, intros i Hi, 
    cases (llvm.ident_eq_dec i x),
    { have Hi : alias_rel am i y, { existsi tp, split; assumption },
      cases (IH i Hi),
      { left, intro H, cases H; cc },
      { right, right, assumption }
    },
    { right, left, assumption },
  },

  cases H,
  { left, intro, clear h IH, apply H, clear H,
    induction a; intros,
    unfold alias_rel at a_a_1, cases a_a_1 with tp' Ha, cases Ha with Ha1 Ha2,
    have Heq : tp = tp', { cc }, subst tp',
    existsi a_a, split, apply Ha2, simp,
    cases (a_ih_a_1 Htp),
    cases h, cases h_right, subst a_b,
    existsi w, split, assumption, right, assumption,
    existsi w, split, assumption, right, apply tc.trans _ a_b _; assumption,
  },
  { right, cases H with i H, cases H with H1 H2, cases H2 with H2 H2,
    subst i, apply tc.base, existsi tp, split; assumption,
    apply tc.trans _ i _, assumption, apply tc.base, existsi tp, split; assumption
  }
end.

lemma string_cmp_using_eq
  (x y : string) :
  cmp_using string.has_lt'.lt x y = ordering.eq → x = y :=
begin
  unfold cmp_using ite,
  cases (string.decidable_lt y x); simp,
  cases (string.decidable_lt x y); simp,
  apply le_antisymm; assumption,
  cases (string.decidable_lt x y); simp,
end.


lemma insert_alias_map_wf_aux
  (am:strmap llvm_type)
  (x z:ident) (tp:llvm_type)
  (Hacc: acc (alias_rel am) z)
  : forall 
  (Hxy : z ≠ x)
  (Hntc: ¬(tc (alias_rel am) x z)),
  acc (alias_rel (rbmap.insert am x.ident tp)) z :=
begin
  apply Hacc.rec_on, clear Hacc z, intros z h IH Hx Htc,
  apply acc.intro, intros q Hq,
  cases Hq with tp Htp, cases Htp with Htp1 Htp2,
  rewrite (rbmap_insert_lookup_neq am) at Htp1,
  { apply IH,
    { existsi tp, cc },
    { intro Hqx, apply Htc, apply tc.base,
      subst q, existsi tp, cc
    },
    { intro Hxq, apply Htc,
      apply tc.trans _ q _, assumption,
      apply tc.base, existsi tp, cc,
    }
  },
  { intro, apply Hx, cases z, cases x, 
    unfold ident.ident at a, 
    have Hzx : z = x, { apply string_cmp_using_eq, assumption },
    cc
  }
end

lemma insert_alias_map_wf
  (am:strmap llvm_type)
  (x:ident) (tp:llvm_type)
  (Hacc: forall a, acc (alias_rel am) a)
  (Hnacc : ¬∃y, y ∈ mentions tp ∧ (y = x ∨ tc (alias_rel am) x y)) 
  : forall a, acc (alias_rel (rbmap.insert am x.ident tp)) a :=
begin
  intro a, apply (Hacc a).rec_on, clear a, intros a h IH, clear h,
  apply acc.intro, intros q Hq,
  cases Hq with tp' Htp, cases Htp with Htp1 Htp2,
  apply (@decidable.by_cases (cmp_using string.has_lt'.lt a.ident x.ident = ordering.eq)); intro Heq,
  { rewrite (rbmap_insert_lookup_eq am x.ident tp) at Htp1; try {assumption},
    injection Htp1, subst tp', clear Htp1,
    apply (insert_alias_map_wf_aux am x q tp (Hacc q)),
    { intro; subst q, apply Hnacc, existsi x, cc, },
    { intro, apply Hnacc, existsi q, cc, }
  },
  { rewrite (rbmap_insert_lookup_neq am x.ident tp) at Htp1; try {assumption},
    apply (IH q), existsi tp', split; assumption
  }
end.

def empty : alias_map := subtype.mk (strmap_empty _)
  begin
    intro a, apply acc.intro, intros b H,
    destruct H, simp, unfold strmap_empty,
    unfold rbmap.find rbmap.find_entry rbmap.from_list, 
    unfold mk_rbmap mk_rbtree, 
    simp, unfold rbmap.find_entry._match_1 rbmap.to_value,
    intros, cc,
  end
.

def insert_check_dec (am:alias_map) (x:ident) (tp:llvm_type) :
  decidable (∃y, y ∈ mentions tp ∧ (y = x ∨ tc (alias_rel am.val) x y)) :=
begin
  apply ex_mem_dec, intros q Hq,
  cases (llvm.ident_eq_dec q x),
  { cases (reachable_dec am.val x q (am.property q)),
    { left, intro H; cases H; cc },
    { right, right, assumption }
  },
  { right, left, assumption }
end.

def insert (am:alias_map) (k:ident) (tp:llvm_type) : option alias_map :=
  match insert_check_dec am k tp with
  | decidable.is_true _ := none
  | decidable.is_false H :=
      some ⟨rbmap.insert am.val k.ident tp, insert_alias_map_wf am.val k tp am.property H⟩
  end

def build : list type_decl → alias_map → sum type_decl alias_map
| []        am := sum.inr am
| (td::tds) am :=
    match insert am td.name td.value with
    | none        := sum.inl td
    | some am'    := build tds am'
    end.

end alias_map.

end llvm.
