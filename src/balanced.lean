import basic
import tactic.linarith
set_option pp.generalized_field_notation false

universe u

namespace balanced
open btree

variables {α : Type u}

lemma easyR_order (xL xR zR : btree α) (x z : nat) (a d : α) :
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
            simp only [forall_keys] at h₆,
            finish, 
          },
          { finish, },
        },
      }, 
    },
    { apply and.intro, 
      { finish, },
      { simp [forall_keys], 
        apply and.intro,
        { finish, },
        { apply and.intro, 
          { sorry },
          { sorry },
        },
      },
    },
  },
end

end balanced