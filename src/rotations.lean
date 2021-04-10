import btree
import balanced
import tactic.linarith
set_option pp.generalized_field_notation false

namespace rotations_lemmas
open balanced
open btree_def

lemma easyR_preserves_order {α : Type} (xL xR zR : btree α) (x z : nat) (a d : α) (h₀ : z < x) :
  ordered (btree.node (btree.node xL x a xR) z d zR) → 
    ordered (easyR (btree.node (btree.node xL x a xR) z d zR)) :=
begin
  intro h₁,
  simp only [easyR, ordered],
  simp only [ordered] at h₁,
  apply and.intro, 
  { apply and.elim_left (and.elim_left h₁) },
  { apply and.intro, 
    { apply and.intro,
      { apply and.elim_left (and.elim_right (and.elim_left h₁)) },
      { apply and.intro,
        { apply and.elim_left (and.elim_right h₁) },
        { apply and.intro, 
          { sorry },
          { apply and.elim_right (and.elim_right (and.elim_right h₁)) }
        }
      } 
    },
    { apply and.intro, 
      { apply and.elim_left (and.elim_right (and.elim_right (and.elim_left h₁))) },
      { simp [forall_keys], 
        apply and.intro,
        { sorry },
        { apply and.intro h₀ (and.elim_right (and.elim_right (and.elim_right h₁))) }
      }
    }
  }
end

lemma easyR_restores_balance {α : Type} (xL xR zR : btree α) (z x : nat) (d a : α) :
  balanced xL ∧ balanced xR ∧ balanced zR ∧ outLeft (btree.node (btree.node xL x a xR) z d zR) → 
    balanced (easyR (btree.node (btree.node xL x a xR) z d zR)) :=
begin
  intro h₁,
  simp only [easyR],
  sorry
end

end rotations_lemmas