import definitions rotations forall_keys tactic.linarith tactic.induction
set_option pp.generalized_field_notation false

universe u

namespace shrink_lemmas 
open btree rotation_lemmas forall_keys_lemmas

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

lemma shrink_keys {t sh : btree α} {x : nat} {a : α} :
  ordered t ∧ shrink t = some (x, a, sh) → bound x t = tt ∧ (∀ k', bound k' sh = tt → bound k' t = tt) :=
begin
  intro h₁,
  cases_matching*  (_ ∧ _),
  induction t generalizing x a sh,
  case empty { contradiction, },
  case node : l k v r ihl ihr {
    rw ordered at h₁_left,
    cases_matching* (_ ∧ _),
    cases' shrink_shrink_view (node l k v r),
    case nonempty_empty {
      cases' h₁_right,
      split,
      { simp [bound], },
      { intros k' h₂, 
        simp [bound], 
        tauto,
      },
     },
    case nonempty_nonempty₁ {
      rw h_2 at h₁_right,
      clear h_2,
      cases' h₁_right,
      specialize ihr h₁_left_right_left h, 
      split,
      { cases_matching* (_ ∧ _),
        simp [bound],
        tauto,
      },
      { intros k' h₂, 
        rw ← rotate_right_keys at h₂,
        simp [bound] at h₂ ⊢,
        tauto,
      },
    },
    case nonempty_nonempty₂ {
      cases' h₁_right,
      specialize ihr h₁_left_right_left h,
      split,
      { cases_matching* (_ ∧ _),
        simp [bound], 
        tauto, 
      },
      { intros k' h₂, 
        simp [bound] at h₂ ⊢,
        tauto,
      },
    },
  },
end

lemma shrink_keys_aux_1 {t sh : btree α} {x : nat} {a : α} :
  ordered t ∧ shrink t = some (x, a, sh) → bound x t :=
begin
  intro h₁,
  apply and.left (shrink_keys h₁),
end

lemma shrink_keys_aux_2 {t sh : btree α} {x : nat} {a : α} :
  ordered t ∧ shrink t = some (x, a, sh) → (∀ k', bound k' sh → bound k' t) :=
begin
  intro h₁,
  apply and.right (shrink_keys h₁),
end

lemma forall_shrink {t sh : btree α} {k x : nat} {a : α} {p : nat → nat → Prop} :
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
      cases' h₁_right,
      rw ← forall_keys_intro at h₁_left,
      cases_matching* (_ ∧ _),
      split; assumption,
    },
    case nonempty_nonempty₁ {
      rw h_2 at h₁_right,
      clear h_2,
      cases' h₁_right,
      rw ← forall_keys_intro at h₁_left,
      cases_matching* (_ ∧ _),
      split,
      { apply forall_rotate_right, 
        rw ← forall_keys_intro,
        repeat { split }; try { assumption },
        { specialize ihr ⟨ h₁_left_right_right, h ⟩, 
          apply and.left ihr,
        },
      },
      { specialize ihr ⟨ h₁_left_right_right, h ⟩, 
        apply and.right ihr,
      },
    },
    case nonempty_nonempty₂ {
      cases' h₁_right,
      rw ← forall_keys_intro at h₁_left,
      cases_matching* (_ ∧ _),
      split,
      { rw ← forall_keys_intro, 
        repeat { split }; try { assumption },
        { specialize ihr ⟨ h₁_left_right_right, h ⟩, 
          apply and.left ihr,
        },
      },
      { specialize ihr ⟨ h₁_left_right_right, h ⟩, 
        apply and.right ihr,
      },
    },
  },
end

lemma forall_shrink_aux_1 {t sh : btree α} {k x : nat} {a : α} {p : nat → nat → Prop} :
  forall_keys p k t ∧ shrink t = some (x, a, sh) → forall_keys p k sh :=
begin
  intro h₁,
  apply and.left (forall_shrink h₁),
end

lemma forall_shrink_aux_2 {t sh : btree α} {k x : nat} {a : α} {p : nat → nat → Prop} :
  forall_keys p k t ∧ shrink t = some (x, a, sh) → p k x :=
begin
  intro h₁,
  apply and.right (forall_shrink h₁),
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
    rw ordered at h₁,
    cases_matching* (_ ∧ _),
    cases' shrink_shrink_view (node l k v r),
    case nonempty_empty { 
      cases' h₁_right,
      split; assumption,
    },
    case nonempty_nonempty₁ {
      rw h_2 at h₁_right,
      clear h_2,
      cases' h₁_right,
      specialize ihr ⟨h₁_left_right_left, h⟩,
      cases_matching* (_ ∧ _),
      split,
      { apply rotate_right_ordered, 
        repeat { split }; try { assumption },
        { apply forall_shrink_aux_1 (and.intro h₁_left_right_right_right h), }
      },
      { apply forall_rotate_right, 
        have h₂ : x_1 > k,
        { have h₃ : bound x_1 r ∧ (∀ k', bound k' sh_1 → bound k' r),
          { apply shrink_keys (and.intro h₁_left_right_left h), },
          cases_matching* (_ ∧ _),
          unfold forall_keys at h₁_left_right_right_right,
          apply h₁_left_right_right_right,
          assumption, 
        },
        have h₃ : forall_keys gt x_1 l,
        { apply forall_keys_trans l (>) k; try { assumption },
          { apply trans, }, 
        },
        rw ← forall_keys_intro,
        repeat { split }; assumption,
      },
    },
    case nonempty_nonempty₂ {
      cases' h₁_right,
      specialize ihr ⟨h₁_left_right_left, h⟩,
      cases_matching* (_ ∧ _),
      split,
      { rw ordered, 
        repeat { split }; try { assumption },
        { apply forall_shrink_aux_1 (and.intro h₁_left_right_right_right h), },
      },
      { have h₂ : x_1 > k,
        { have h₃ : bound x_1 r ∧ (∀ k', bound k' sh_1 → bound k' r),
          { apply shrink_keys (and.intro h₁_left_right_left h), },
          cases_matching* (_ ∧ _), 
          unfold forall_keys at h₁_left_right_right_right,
          apply h₁_left_right_right_right,
          assumption,
        },
        have h₃ : forall_keys gt x_1 l,
        { apply forall_keys_trans l (>) k; try { assumption },
          { apply trans, },
        },
        rw ← forall_keys_intro,
        repeat { split }; assumption,
      },
    },
  },
end

lemma shrink_ordered_aux_1 {t sh : btree α} {x : nat} {a : α} :
  ordered t ∧ shrink t = some (x, a, sh) → ordered sh :=
begin
  intro h₁,
  apply and.left (shrink_ordered h₁), 
end

lemma shrink_ordered_aux_2 {t sh : btree α} {x : nat} {a : α} :
  ordered t ∧ shrink t = some (x, a, sh) → forall_keys (>) x sh :=
begin
  intro h₁,
  apply and.right (shrink_ordered h₁),
end

end shrink_lemmas