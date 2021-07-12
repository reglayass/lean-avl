import definitions tactic.linarith
set_option pp.generalized_field_notation false

universe u

namespace forall_keys_lemmas
open btree

variables {α : Type u}

/- Transivitity property for keys in a binary search tree -/
lemma forall_keys_trans (t : btree α) (p : nat → nat → Prop) (z x : nat) (h₁ : p x z) (h₂ : ∀ a b c, p a b → p b c → p a c) :
  forall_keys p z t → forall_keys p x t :=
begin
  unfold forall_keys,
  intros h₃ k' h₄,
  apply h₂ _ _ _ h₁,
  apply h₃,
  exact h₄,
end

/- Lemma to equre forall_keys_unfolded to the bound version -/
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

/- Lemma to equate forall_keys to the unfolded version -/
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
  (forall_keys p k l ∧ p k x ∧ forall_keys p k r) ↔ forall_keys p k (node l x v r) :=
begin
  split,
  { intro h₁, 
    cases_matching* (_ ∧ _),
    unfold forall_keys at *,
    intros k' h₂,
    simp [bound] at h₂,
    cases_matching* (_ ∨ _),
    { subst h₂, exact h₁_right_left, },
    { apply h₁_left, exact h₂, },
    { apply h₁_right_right, exact h₂, },
  },
  { intro h₁,
    unfold forall_keys at h₁ ⊢,
    repeat { split },
    { intros k' h₂,
      apply h₁,
      simp [bound],
      tauto,
    },
    { apply h₁, 
      simp [bound],
    },
    { intros k' h₂, 
      apply h₁,
      simp [bound],
      tauto,
    },
  },
end

end forall_keys_lemmas