import btree
import ordered
import tactic.linarith
set_option pp.generalized_field_notation false

namespace balanced
open btree ordered

/-- 
  Height of a tree 
-/
def height {α : Type} : btree α → nat
| btree.empty := 0
| (btree.node l k a r) :=
  1 + (max (height l) (height r))

/--
  Definition of a balanced tree
-/
def balanced {α : Type} : btree α → bool
| btree.empty := tt
| (btree.node l k a r) := (height l - height r) ≤ 1

/-- 
  Definition of a tree being outside left-heavy
-/
def outLeft {α : Type} : btree α → bool
| btree.empty := ff
| (btree.node (btree.node xL x a xR) z d zR) := 
  (height xL ≥ height xR) ∧ (height xL ≤ height xR + 1) ∧ 
  (height xR ≥ height zR) ∧ (height xL = height zR + 1)
| (btree.node l k a r) := ff

-- inductive outLeft' {α : Type} : btree α → Prop
-- | intro (xL xR zR : btree α) (x z : nat) (a d : α) :  
--     (height xL ≥ height xR) → 
--     (height xL ≤ height xR + 1) → 
--     (height xR ≥ height zR) → 
--     (height xL = height zR + 1) → 
--     outLeft' (btree.node (btree.node xL x a xR) z d zR)

/--
  Definition of a tree being outside right-heavy
-/
def outRight {α : Type} : btree α → bool
| btree.empty := ff
| (btree.node zL z d (btree.node yL y b yR)) :=
  (height yL ≤ height yR) ∧ (height yL ≤ height yR + 1) ∧
  (height yR ≥ height zL) ∧ (height zL + 1 = height yR)
| (btree.node l k a r) := ff

/--
  Simple right rotation
-/
def easyR {α : Type} : btree α → btree α
| btree.empty := btree.empty
| (btree.node (btree.node xL x a xR) z d zR) := 
  (btree.node xL x a (btree.node xR z d zR))
| (btree.node l k a r) := btree.node l k a r


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

/--
  Simple left rotation
-/
def easyL {α : Type} : btree α → btree α
| btree.empty := btree.empty
| (btree.node zL z d (btree.node yL y b yR)) :=
  (btree.node (btree.node zL z d yL) y b yR)
| (btree.node l k a r) := btree.node l k a r

/--
  Definition of a right rotation
  If the right subtree is bigger in height than the 
  left subtree, then a double rotation is done.
  Otherwise, a simple right rotation will do.
-/
def rotR {α : Type} : btree α → btree α
| btree.empty := btree.empty
| (btree.node (btree.node xL x a xR) z d zR) :=
  if (height xL < height xR) then easyR (btree.node (easyL (btree.node xL x a xR)) z d zR)
  else easyR (btree.node (btree.node xL x a xR) z d zR)
| (btree.node l k a r) := btree.node (rotR l) k a r

/--
  Definition of a left rotation
  If the left subtree is bigger in height
  than the right subtree, then a double rotation is done.
  Otherwise, a simple left rotation will do. 
-/
def rotL {α : Type} : btree α → btree α
| btree.empty := btree.empty
| (btree.node zL z d (btree.node yL y b yR)) :=
  if (height yR < height yL) then easyL (btree.node zL z d (easyR (btree.node yL y b yR)))
  else easyL (btree.node zL z d (btree.node yL y b yR))
| (btree.node l k a r) := btree.node l k a (rotL r)

end balanced