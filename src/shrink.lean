import definitions
import rotations
import tactic.linarith
import tactic.induction
set_option pp.generalized_field_notation false

universe u

namespace shrink_lemmas 
open btree
open rotation_lemmas

variables {α : Type u}

lemma shrink_shrink_view (t : btree α) : 
  shrink_view t (shrink t) :=
begin
 cases t,
 case empty {
  exact shrink_view.empty,
 },
 case node : l k a r {
  dsimp [shrink],
  cases h : shrink r,
  case none {
    dsimp only [shrink._match_1],
    apply shrink_view.nonempty_empty; assumption,
  },
  case some {
    rcases val with ⟨x, a', sh⟩,
    dsimp only [shrink._match_1],
    by_cases h' : (height l > height sh + 1),
    { simp only [if_pos h'], 
      apply shrink_view.nonempty_nonempty₁, try { assumption },
      assumption, simp,
    },
    { simp only [if_neg h'],
      apply shrink_view.nonempty_nonempty₂, try { assumption },
      linarith,
    },
  },
 },
end

lemma forall_keys_shrink {t sh : btree α} {k x : nat} {a : α} {p : nat → nat → Prop} :
  forall_keys p k t → shrink t = some (x, a, sh) → forall_keys p k sh ∧ p k x :=
begin
  intros h₁ h₂,
  induction t generalizing x a sh,
  case empty {
    contradiction,
  },
  case node : l k v r ihl ihr {
    cases' shrink_shrink_view (node l k v r),
    { cases' h₂, 
      rw forall_keys at h₁,
      split, 
      { apply and.left h₁, },
      { apply and.left (and.right h₁), },
    },
    { rw h_2 at h₂, 
      rw forall_keys at h₁,
      sorry,
    },
    { sorry },
  },
end

lemma forall_keys_shrink_aux_1 {t sh : btree α} {k x : nat} {a : α} {p : nat → nat → Prop} :
  forall_keys p k t → shrink t = some (x, a, sh) → forall_keys p k sh :=
begin
  intros h₁ h₂,
  have h : forall_keys p k sh ∧ p k x := forall_keys_shrink h₁ h₂,
  apply and.left h,
end

lemma forall_keys_shrink_aux_2 {t sh : btree α} {k x : nat} {a : α} {p : nat → nat → Prop} :
  forall_keys p k t → shrink t = some (x, a, sh) → p k x :=
begin
  intros h₁ h₂,
  have h : forall_keys p k sh ∧ p k x := forall_keys_shrink h₁ h₂,
  apply and.right h,
end

lemma shrink_ordered {t sh : btree α} {k x : nat} {a : α} :
  ordered t ∧ shrink t = some (x, a, sh) → ordered sh ∧ forall_keys (>) x sh :=
begin
  intro h₁,
  induction t generalizing x a sh,
  case empty {
    cases_matching* (_ ∧ _),
    contradiction,
  },
  case node : l k v r ihl ihr {
    cases_matching* (_ ∧ _),
    cases' shrink_shrink_view (node l k v r),
    case nonempty_empty {
      cases' h₁_right,
      rw ordered at h₁_left,
      cases_matching* (_ ∧ _),
      repeat { split }; assumption,
    },
    case nonempty_nonempty₁ {
      rw h_2 at h₁_right,
      clear h_2,
      cases' h₁_right,
      rw ordered at h₁_left,
      cases_matching* (_ ∧ _),
      specialize ihr ⟨h₁_left_right_left, h⟩,
      split,
      { apply rotate_right_ordered, 
        rw ordered,
        cases_matching* (_ ∧ _),
        repeat { split }; try { assumption },
        apply forall_keys_shrink_aux_1 h₁_left_right_right_right h,
      },
      { apply forall_rotate_right, 
        rw forall_keys,
        repeat { split },
        { sorry },
        { sorry },
        { apply and.right ihr, },
      }, 
    },
    case nonempty_nonempty₂ { sorry },
  },
end

lemma shrink_ordered_aux_1 {t sh : btree α} {k x : nat} {a : α} :
  ordered t ∧ shrink t = some (x, a, sh) → ordered sh :=
begin
  intro h₁,
  have h : ordered sh ∧ forall_keys (>) x sh := shrink_ordered h₁,
  { apply and.left h, },
  { exact x, },
end

lemma shrink_ordered_aux_2 {t sh : btree α} {k x : nat} {a : α} :
  ordered t ∧ shrink t = some (x, a, sh) → forall_keys (>) x sh :=
begin
  intro h₁,
  have h : ordered sh ∧ forall_keys (>) x sh := shrink_ordered h₁,
  { apply and.right h, },
  { exact x, },
end

end shrink_lemmas