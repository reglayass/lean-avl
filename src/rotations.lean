import basic
import tactic.linarith
set_option pp.generalized_field_notation false

universe u

namespace rotation_lemmas
open btree

variables {α : Type u}

lemma easyR_ordered (xL xR zR : btree α) (x z : nat) (a d : α) : 
  ordered (btree.node (btree.node xL x a xR) z d zR) → 
    ordered (easyR (btree.node (btree.node xL x a xR) z d zR)) :=
begin
  intro h₁,
  simp only [easyR, ordered],
  simp only [ordered] at h₁,
  apply and.intro,
  { finish, },
  { apply and.intro,
    { apply and.intro, 
      { finish, },
      { apply and.intro, 
        { finish, },
        { apply and.intro,
          { apply and.elim h₁, 
            intros h₂ h₃,
            apply and.elim h₃,
            intros h₄ h₅,
            apply and.elim h₅,
            intros h₆ h₇,
            rw forall_keys at h₆,
            finish,
          },
          { finish, } 
        }
      }
    },
    { apply and.intro, 
      { finish, },
      { rw forall_keys, sorry }
    } 
  }
end

lemma easyR_keys (xL xR zR : btree α) (k x z : nat) (a d : α) :
  bound k (btree.node (btree.node xL x a xR) z d zR) →
    bound k (easyR (btree.node (btree.node xL x a xR) z d zR)) :=
begin
  sorry
end

-- lemma easyR_preserves_order (xL xR zR : btree α) (k x z : nat) (a d : α) :
--   outLeft (btree.node (btree.node xL x a xR) z d zR) →
--     balanced (easyR (btree.node (btree.node xL x a xR) z d zR)) :=
-- begin
--   intro h₁,
--   simp [easyR, balanced],
--   simp [outLeft] at h₁,
--   sorry
-- end  

end rotation_lemmas