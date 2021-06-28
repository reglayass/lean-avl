import definitions
import rotations
import ordered
import tactic.linarith
import tactic.induction
set_option pp.generalized_field_notation false

universe u

namespace shrink_lemmas 
open btree
open rotation_lemmas
open ordered

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

lemma forall_keys_unfolded_bound (t : btree α) (p : nat → nat → Prop) (k : nat) :
  forall_keys_unfolded p k t → forall_keys p k t :=
begin
  intro h₁,
  induction t,
  case empty {
    simp [forall_keys, bound],
  },
  case node : l x v r ihl ihr {
    unfold forall_keys at *,
    rw forall_keys_unfolded at h₁,
    cases_matching* (_ ∧ _),
    intros k' h₂,
    simp [bound] at h₂,
    cases_matching* (_ ∨ _),
    { subst h₂, assumption, },
    { apply ihl; assumption, },
    { apply ihr; assumption, },
  },
end

lemma forall_keys_bound_unfolded (t : btree α) (p : nat → nat → Prop) (k : nat) :
  forall_keys p k t → forall_keys_unfolded p k t :=
begin
  intro h₁,
  induction t,
  case empty {
    simp [forall_keys_unfolded],
  },
  case node : l x v r ihl ihr {
    rw forall_keys_unfolded,
    simp [forall_keys] at ihl ihr h₁,
    repeat { split },
    { apply ihl, 
      intros k' h₂,
      apply h₁,
      simp [bound], tauto,
    },
    { apply h₁, 
      simp [bound],
    },
    { apply ihr, 
      intros k' h₂,
      apply h₁,
      simp [bound], tauto,
    },
  },
end

lemma forall_keys_intro {l r : btree α} {k x : nat} {v : α} {p : nat → nat → Prop} :
  (forall_keys p k l ∧ p k x ∧ forall_keys p k r) → forall_keys p k (node l x v r) :=
begin
  intro h₁,
  cases_matching* (_ ∧ _),
  unfold forall_keys at *,
  intros k' h₂,
  simp [bound] at h₂,
  cases_matching* (_ ∨ _),
  { subst h₂, 
    exact h₁_right_left,
  },
  { apply h₁_left, 
    exact h₂,
  },
  { apply h₁_right_right, 
    exact h₂,
  },
end

lemma forall_keys_shrink {t sh : btree α} {k x : nat} {a : α} {p : nat → nat → Prop} :
  forall_keys p k t ∧ shrink t = some (x, a, sh) → forall_keys p k sh ∧ p k x :=
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
    case nonempty_empty { sorry },
    case nonempty_nonempty₁ {
      rw h_2 at h₁_right,
      clear h_2,
      cases' h₁_right,
      sorry,
    },
    case nonempty_nonempty₂ { sorry },
  },
end

lemma forall_keys_shrink_aux_1 {t sh : btree α} {k x : nat} {a : α} {p : nat → nat → Prop} :
  forall_keys p k t ∧ shrink t = some (x, a, sh) → forall_keys p k sh :=
begin
  intro h₁,
  have h : forall_keys p k sh ∧ p k x := forall_keys_shrink h₁,
  apply and.left h,
end

lemma forall_keys_shrink_aux_2 {t sh : btree α} {k x : nat} {a : α} {p : nat → nat → Prop} :
  forall_keys p k t ∧ shrink t = some (x, a, sh) → p k x :=
begin
  intro h₁,
  have h : forall_keys p k sh ∧ p k x := forall_keys_shrink h₁,
  apply and.right h,
end

lemma shrink_keys {t sh : btree α} {x : nat} {a : α} :
  ordered t → shrink t = some (x, a, sh) → bound x t ∧ (∀ k', bound k' sh → bound k' t) :=
begin
  intros h₁ h₂,
  induction t generalizing x a sh,
  case empty {
    cases_matching* (_ ∧ _),
    contradiction,
  },
  case node : l k v r ihl ihr {
    cases_matching* (_ ∧ _),
    cases' shrink_shrink_view (node l k v r),
    case nonempty_empty { 
      sorry,
    },
    case nonempty_nonempty₁ {
      rw ordered at h₁,
      cases_matching* (_ ∧ _),
      rw h_2 at h₂,
      cases h₂,
      specialize ihr h₁_right_left h,
      cases_matching* (_ ∧ _),
      split,
      { simp [bound],
        apply or.inr (or.inr ihr_left),
      },
      { sorry },
    },
    case nonempty_nonempty₂ {
      rw ordered at h₁,
      cases_matching* (_ ∧ _),
      cases' h₂,
      specialize ihr h₁_right_left h,
      cases_matching* (_ ∧ _),
      split,
      { simp [bound], 
        apply or.inr (or.inr ihr_left),
      },
      { sorry },
    },
  },
end

lemma shrink_ordered {t sh : btree α} {x : nat} {a : α} :
  ordered t ∧ shrink t = some (x, a, sh) → ordered sh ∧ forall_keys gt x sh :=
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
      cases_matching* (_ ∧ _),
      split,
      { apply rotate_right_ordered, 
        repeat { split }; try { assumption },
        { apply forall_keys_shrink_aux_1 (and.intro h₁_left_right_right_right h), },
      }, 
      { apply forall_rotate_right, 
        have g₂ : x_1 > k,
        { have h₃ : bound x_1 r ∧ (∀ k', bound k' sh_1 → bound k' r), 
          { apply shrink_keys h₁_left_right_left h, },
          cases_matching* (_ ∧ _),
          unfold forall_keys at h₁_left_right_right_right,
          apply h₁_left_right_right_right,
          assumption,
        },
        have g₃ : forall_keys gt x_1 l,
        { apply forall_keys_trans l (>) k,
          { assumption, },
          { apply trans, },
          { assumption, },
        },
        apply forall_keys_intro,
        repeat { split }; assumption,
      },
    },
    case nonempty_nonempty₂ {
      cases' h₁_right,
      rw ordered at h₁_left,
      cases_matching* (_ ∧ _),
      specialize ihr ⟨h₁_left_right_left, h⟩,
      cases_matching* (_ ∧ _),
      split,
      { rw ordered, 
        repeat { split }; try { assumption },
        { apply forall_keys_shrink_aux_1 (and.intro h₁_left_right_right_right h), },
      },
      { have g₂ : x_1 > k,
        { have h₃ : bound x_1 r ∧ (∀ k', bound k' sh_1 → bound k' r), 
          { apply shrink_keys h₁_left_right_left h, },
          cases_matching* (_ ∧ _),
          unfold forall_keys at h₁_left_right_right_right,
          apply h₁_left_right_right_right,
          assumption,
        },
        have g₃ : forall_keys gt x_1 l,
        { apply forall_keys_trans l (>) k, 
          { assumption, },
          { apply trans, },
          { assumption, },
        },
        apply forall_keys_intro,
        repeat { split }; assumption,
      },
    },
  },
end

lemma shrink_ordered_aux_1 {t sh : btree α} {x : nat} {a : α} :
  ordered t ∧ shrink t = some (x, a, sh) → ordered sh :=
begin
  intro h₁,
  have h : ordered sh ∧ forall_keys (>) x sh := shrink_ordered h₁,
  { apply and.left h, },
end

lemma shrink_ordered_aux_2 {t sh : btree α} {x : nat} {a : α} :
  ordered t ∧ shrink t = some (x, a, sh) → forall_keys (>) x sh :=
begin
  intro h₁,
  have h : ordered sh ∧ forall_keys (>) x sh := shrink_ordered h₁,
  { apply and.right h, },
end

end shrink_lemmas