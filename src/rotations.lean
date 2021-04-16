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
          { sorry },
          { finish, } 
        }
      }
    },
    { apply and.intro, 
      { finish, },
      { sorry }
    } 
  }
end

end rotation_lemmas