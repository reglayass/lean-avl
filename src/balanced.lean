import btree
import tactic.linarith
set_option pp.generalized_field_notation false

namespace balanced
open btree_def

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

def leftHeavy : btree string := btree.node (btree.node (btree.node btree.empty 1 "c" btree.empty) 2 "b" btree.empty) 3 "a" btree.empty

/-- 
  Definition of a tree being outside left-heavy
-/
def outLeft {α : Type} : btree α → bool
| btree.empty := ff
| (btree.node (btree.node xL x a xR) z d zR) := 
  (height xL ≥ height xR) ∧ (height xL ≤ height xR + 1) ∧ 
  (height xR ≥ height zR) ∧ (height xL = height zR + 1)
| (btree.node l k a r) := ff

inductive outLeft' {α : Type} : btree α → Prop
| intro (xL xR zR : btree α) (x z : nat) (a d : α) :  
    (height xL ≥ height xR) → 
    (height xL ≤ height xR + 1) → 
    (height xR ≥ height zR) → 
    (height xL = height zR + 1) → 
    outLeft' (btree.node (btree.node xL x a xR) z d zR)

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