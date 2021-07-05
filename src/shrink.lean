import definitions
import rotations
import forall_keys
import tactic.linarith
import tactic.induction
set_option pp.generalized_field_notation false

universe u

namespace shrink_lemmas 
open btree
open rotation_lemmas
open forall_keys_lemmas

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
    case nonempty_empty {
      sorry
    },
    case nonempty_nonempty₁ {
      rw h_2 at h₁_right,
      clear h_2,
      cases' h₁_right,
      split,
      { apply forall_rotate_right, 
        apply forall_keys_intro,
        unfold forall_keys at h₁_left,
        repeat { split },
        { unfold forall_keys, 
          intros k' h₂,
          apply h₁_left,
          simp [bound],
          apply or.inr (or.inl h₂),
        },
        { apply h₁_left, 
          simp [bound],
        },
        { sorry },
      },
      { sorry },
    },
    case nonempty_nonempty₂ {
      cases' h₁_right,
      split,
      { apply forall_keys_intro, 
        unfold forall_keys at h₁_left,
        repeat { split },
        { unfold forall_keys,
          intros k' h₂,
          apply h₁_left,
          simp [bound],
          apply or.inr (or.inl h₂),
        },
        { apply h₁_left,
          simp [bound],
        },
        { sorry },
      },
      { sorry },
    },
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
    rw ordered at h₁,
    cases_matching* (_ ∧ _),
    cases' shrink_shrink_view (node l k v r),
    case nonempty_empty {
      sorry,
    },
    case nonempty_nonempty₁ {
      rw h_2 at h₂,
      clear h_2,
      cases' h₂,
      specialize ihr h₁_right_left h,
      cases_matching* (_ ∧ _),
      specialize ihr_right x_1,
      split,
      { simp [bound], 
        apply or.inr (or.inr ihr_left),
      },
      { sorry, },
    },
    case nonempty_nonempty₂ {
      cases' h₂,
      specialize ihr h₁_right_left h,
      cases_matching* (_ ∧ _),
      specialize ihr_right x_1,
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