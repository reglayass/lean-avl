import definitions
import tactic.linarith
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

/- Order of keys previously existing does not change on new key insertion -/
lemma forall_insert (k x : nat) (t : btree α) (a : α) (p : nat → nat → Prop) (h : p x k) :
  forall_keys p x t → forall_keys p x (insert k a t) :=
begin
  unfold forall_keys,
  intros h₁ k' h₂,
  induction t,
  case empty {
    simp [btree.insert, bound] at h₂,
    subst h₂,
    exact h,
  },
  case node : tl tk ta tr ihl ihr {
    simp [btree.insert] at h₂,
    by_cases c₁ : (k < tk),
    { simp [if_pos c₁, bound] at h₂,
      cases_matching* (_ ∨ _),
      { apply h₁, 
        simp [bound],
        apply or.inl h₂,
      },
      { apply ihl,
        { intros k' h₃, apply h₁,
          simp [bound],
          apply or.inr (or.inl h₃),
        },
        { exact h₂, }, 
      },
      { apply h₁, 
        simp [bound],
        apply or.inr (or.inr h₂),
      },
    },
    { simp only [if_neg c₁] at h₂, 
      by_cases c₂ : (tk < k),
      { simp [if_pos c₂, bound] at h₂, 
        cases_matching* (_ ∨ _),
        { apply h₁, 
          simp [bound],
          apply or.inl h₂,
        },
        { apply h₁, 
          simp [bound],
          apply or.inr (or.inl h₂),
        },
        { apply ihr, 
          { intros k' h₃, 
            apply h₁,
            simp [bound],
            apply or.inr (or.inr h₃),
          },
          { exact h₂ },
        },
      },
      { simp only [if_neg c₂] at h₂, 
        apply h₁,
        have h : tk = k := by linarith,
        subst h,
        exact h₂,
      },
    },
  },
end 

end forall_keys_lemmas