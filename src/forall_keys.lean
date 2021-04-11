import btree
import tactic.linarith
set_option pp.generalized_field_notation false

namespace forall_keys_lemmas
open btree_def

lemma forall_insert {α : Type} (k k' : nat) (t : btree α) (a : α) (p : nat → nat → Prop) (h₀ : p k' k) :
  forall_keys p k' t → forall_keys p k' (insert k a t) :=
begin
  intro h₁,
  induction t,
  case empty {
    simp only [btree_def.insert, forall_keys],
    simp only [forall_keys] at h₁,
    apply and.intro h₁ (and.intro h₀ h₁)
  },
  case node : tl tk ta tr ihl ihr {
    simp only [btree_def.insert],
    simp only [forall_keys] at h₁,
    by_cases c₁ : (k < tk),
    { simp only [if_pos c₁, forall_keys], 
      apply and.intro,
      { apply ihl, 
        apply and.elim_left h₁,
      },
      { apply and.elim_right h₁ }
    },
    { simp only [if_neg c₁],
      by_cases c₂ : (k > tk),
      { simp only [if_pos c₂], 
        simp only [forall_keys],
        apply and.intro,
        { apply and.elim_left h₁ },
        { apply and.intro, 
          { apply and.elim_left (and.elim_right h₁) },
          { apply ihr,
            apply and.elim_right (and.elim_right h₁),
          }
        }
      },
      { simp only [if_neg c₂, forall_keys],
        apply and.intro,
        { apply and.elim_left h₁ },
        { apply and.intro,
          { exact h₀ },
          { apply and.elim_right (and.elim_right h₁) } 
        }
      } 
    }
  },
end

end forall_keys_lemmas