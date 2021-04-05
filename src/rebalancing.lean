import btree
import tactic.linarith
set_option pp.generalized_field_notation false

namespace rebalancing
open btree_def

#check list

-- outLeft (Cel z d (Cel x a xL xR) zR) =
-- (height (xL) ≥ height (xR)) ∧ (height (xL) ≤ height (xR) + 1) ∧ (height (xR) ≥ height (zR)) ∧ (height (xL) = height (zR) + 1)

def outLeft {α : Type} : btree α → bool
| btree.empty := ff
| (btree.node (btree.node xL x a xR) z d zR) :=
  (height xL ≥ height xR) ∧ (height xL ≤ height xR + 1) ∧ 
  (height xR ≥ height zR) ∧ (height xL = height xR + 1)
| (btree.node _ _ _ _) := ff

def ex_tree_left_heavy : btree string := 
  btree.node 
    (btree.node (btree.node (btree.node empty_tree 2 "data2" empty_tree) 3 "data3" empty_tree) 4 "data4" (btree.node empty_tree 6 "data6" empty_tree)) 5 "data5" (btree.node empty_tree 7 "data7" empty_tree)

def ex_tree_not_left_heavy : btree string :=
  btree.node (btree.node empty_tree 4 "data4" empty_tree) 5 "data5" (btree.node empty_tree 7 "data7" empty_tree)

def empty_tree : btree string := btree.empty

-- easyR (Cel z d (Cel x a xL xR) zR) = (Cel x a xL (Cel z d xR zR))

-- easyR (Cel z d (Cel x a xL xR) zR) = (Cel x a xL (Cel z d xR zR))
-- def easyR {α : Type} : btree α → btree α
-- | btree.empty := btree.empty
-- | (btree.node (btree.node xL x a xR) z d zR) := 
--   (btree.node xL x a (btree.node xR z d zR))
-- | (btree.node l k a r) := btree.node l k a r

-- easyL (Cel z d zL (Cel y b yL yR)) = (Cel y b (Cel z d zL yL) yR)
-- def easyL {α : Type} : btree α → btree α
-- | btree.empty := btree.empty
-- | (btree.node zL z d (btree.node yL y b yR)) := 
--   (btree.node (btree.node zL z d yL) y b yR)
-- | (btree.node l k a r) := btree.node l k a r

-- outLeft (Cel z d (Cel x a xL xR) zR) =
-- (height (xL) ≥ height (xR)) ∧ (height (xL) ≤ height (xR) + 1) ∧ (height (xR) ≥ height (zR)) ∧ (height (xL) = height (zR) + 1)
-- def outLeft {α : Type} : btree α → bool
-- | btree.empty := ff
-- | (btree.node (btree.node xL x a xR) z d zR) := 
--   (height xL ≥ height xR) ∧ (height xL ≤ height xR + 1) ∧ 
--   (height xR ≥ height zR) ∧ (height xL = height zR + 1)
-- | (btree.node _ _ _ _) := ff


-- def insert_balanced {α : Type} (x : nat) (a : α) : btree α → btree α
-- | btree.empty := btree.node btree.empty x a btree.empty
-- | (btree.node l k a' r) :=
--   if x < k then 
--     if outLeft (btree.node (insert x a l) k a' r) then sorry
--     else btree.node (insert x a l) k a' r
--   else if x < k then sorry
--   else btree.node l x a r

end rebalancing