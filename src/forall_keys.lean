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

/- Characterization lemma to unfold forall_keys into two different children  -/
lemma forall_keys_char {l r : btree α} {k x : nat} {v : α} {p : nat → nat → Prop} :
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