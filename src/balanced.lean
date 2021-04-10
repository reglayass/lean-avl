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

/--
  Simple right rotation
-/
def easyR {α : Type} : btree α → btree α
| btree.empty := btree.empty
| (btree.node (btree.node xL x a xR) z d zR) := 
  (btree.node xL x a (btree.node xR z d zR))
| (btree.node l k a r) := btree.node l k a r

-- /--
--   Insertion with balancing
-- -/
-- def insert {α : Type} (x : nat) (a : α) : btree α → btree α
-- | btree.empty := btree.node btree.empty x a btree.empty
-- | (btree.node l k a' r) :=
--   if x < k then 
--     if outLeft (btree.node (insert l) k a' r) then easyR (btree.node (insert l) k a' r)
--     else btree.node (insert l) k a' r
--   else if x > k then sorry
--   else btree.node l x a r

end balanced