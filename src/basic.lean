universe u

/--
  Inductive type: Binary Tree 
  Either consists of an empty tree, or a node that 
  has a key, data, and a left and right subtree.
-/
inductive btree (α : Type u)
| empty {} : btree
| node (l : btree) (k : nat) (a : α) (r : btree) : btree

namespace btree
variables {α : Type u}

/-- 
  Definition of an empty tree
-/
def empty_tree : btree α := btree.empty

/--
  Looking up in a tree
  If the key is smaller than the given node, then look in the left subtree
  Otherwise, look in the right subtree
-/
def lookup (x : nat) : btree α → option α 
| btree.empty := none
| (btree.node l k a r) :=
  if x < k then lookup l
  else if x > k then lookup r
  else a

/--
  A key cannot be bound to an empty tree. 
  If the key that is bound is smaller than the key of the node,
  then it is bound in the left tree. Else, it is bound in the right tree
-/
def bound (x : nat) : btree α → bool
| btree.empty := ff
| (btree.node l k a r) :=
  if x < k then bound l
  else if x > k then bound r 
  else tt 

/--
  Insertion into a binary search tree
  If the tree is empty, then you insert one node with empty subtrees
  If the key is smaller than the root node, then insert in the left subtree
  Else, insert in the right subtree.
-/
def insert (x : nat) (a : α) : btree α → btree α
| btree.empty := btree.node btree.empty x a btree.empty
| (btree.node l k a' r) :=
  if x < k then btree.node (insert l) k a' r 
  else if x > k then btree.node l k a' (insert r)
  else btree.node l x a r

section ordering

def forall_keys (p : nat → nat → Prop) : nat → btree α → Prop
| x btree.empty := tt
| x (btree.node l k a r) :=
  forall_keys x l ∧ (p x k) ∧ forall_keys x r

/--
  A binary tree is ordered when both left and right subtrees of the
  root node satisfy the predicate that each left subtree has keys
  less than the root, and each right subtree has keys more than the root.
-/
def ordered {α: Type} : btree α → Prop
| btree.empty := tt
| (btree.node l k a r) := ordered l ∧ ordered r ∧ (forall_keys (>) k l) ∧ (forall_keys (<) k r)

end ordering

section balancing

/-- 
  Height of a tree 
-/
def height : btree α → nat
| btree.empty := 0
| (btree.node l k a r) :=
  1 + (max (height l) (height r))

/--
  Definition of a balanced tree
-/
def balanced : btree α → bool
| btree.empty := tt
| (btree.node l k a r) := (height l - height r) ≤ 1

/-- 
  Definition of a tree being outside left-heavy
-/
def outLeft : btree α → bool
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
def outRight : btree α → bool
| btree.empty := ff
| (btree.node zL z d (btree.node yL y b yR)) :=
  (height yL ≤ height yR) ∧ (height yL ≤ height yR + 1) ∧
  (height yR ≥ height zL) ∧ (height zL + 1 = height yR)
| (btree.node l k a r) := ff

/--
  Simple right rotation
-/
def easyR : btree α → btree α
| btree.empty := btree.empty
| (btree.node (btree.node xL x a xR) z d zR) := 
  (btree.node xL x a (btree.node xR z d zR))
| (btree.node l k a r) := btree.node l k a r

/--
  Simple left rotation
-/
def easyL : btree α → btree α
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
def rotR : btree α → btree α
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
def rotL : btree α → btree α
| btree.empty := btree.empty
| (btree.node zL z d (btree.node yL y b yR)) :=
  if (height yR < height yL) then easyL (btree.node zL z d (easyR (btree.node yL y b yR)))
  else easyL (btree.node zL z d (btree.node yL y b yR))
| (btree.node l k a r) := btree.node l k a (rotL r)

end balancing

end btree