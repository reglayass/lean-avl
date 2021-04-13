import basic
import tactic.linarith
set_option pp.generalized_field_notation false

universe u

namespace balanced
open btree

variable {α : Type u}

lemma easyR_order {α : Type} (xL xR zR : btree α) (x z : nat) (a d : α) :
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
        { sorry },
        { sorry }
      }
    },
    { apply and.intro, 
      { finish, },
      { simp only [forall_keys],
        sorry
      }
    }
  }
end

lemma easyR_balance {α : Type} (xL xR zR : btree α) (x z : nat) (a d : α) :
  outLeft (btree.node (btree.node xL x a xR) z d zR) → 
    balanced (easyR (btree.node (btree.node xL x a xR) z d zR)) :=
begin
  intro h₁,
  simp [easyR, balanced],
  simp [outLeft] at h₁, 
  sorry
end

lemma easyR_keys {α : Type} (xL xR zR : btree α) (x z k : nat) (a d : α) :
  bound k (btree.node (btree.node xL x a xR) z d zR) → 
    bound k (easyR (btree.node (btree.node xL x a xR) z d zR)) :=
begin
  sorry
end

end balanced