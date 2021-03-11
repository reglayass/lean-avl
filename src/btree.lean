namespace btree_def

/- # Binary Tree -/

/--
  Inductive type: Binary Tree 
  Either consists of an empty tree, or a node that 
  has a key, data, and a left and right subtree.
-/
inductive btree (α: Type) : Type
| empty {} : btree
| node (l : btree) (k : nat) (a : α) (r : btree) : btree

/--
  Definition of an empty tree
-/
def empty_tree {α : Type} : btree α :=
  btree.empty

/--
  Looking up in a tree
  If the key is smaller than the given node, then look in the left subtree
  Otherwise, look in the right subtree
-/
def lookup {α : Type} (x : nat) : btree α → option α
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
def bound {α : Type} (x : nat) : btree α → bool
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
def insert {α : Type} (x : nat) (a : α) : btree α → btree α
| btree.empty := btree.node btree.empty x a btree.empty
| (btree.node l k a' r) :=
  if x < k then btree.node (insert l) k a' r 
  else if x > k then btree.node l k a' (insert r)
  else btree.node l x a r

/--
  A binary tree is ordered when both left and right subtrees of the
  root node satisfy the predicate that each left subtree has keys
  less than the root, and each right subtree has keys more than the root.
-/
def ordered {α: Type} (p : nat → btree α → Prop) : btree α → Prop
| btree.empty := tt
| (btree.node l k a r) := (ordered l) ∧ (ordered r) ∧ (p k l) ∧ (p k r)

/--
  Number of elements that are bound to a specific key
  In any search tree, if a key is bound to a tree then the list 
  of elements will be one
-/
def treeElems {α : Type} : btree α → nat → list α
| btree.empty x := []
| (btree.node l k a r) x := 
  if x = k then append (a :: (treeElems l x)) (treeElems r x)
  else append (treeElems l x) (treeElems r x)

/-- 
  Height of a tree 
-/
def height {α : Type} : btree α → nat
| btree.empty := 0
| (btree.node l k a r) :=
  1 + (max (height l) (height r))

/- # Ordered Binary Search Tree -/

-- inductive bst {α : Type} (l : btree α) (x : nat) (a : α) (r : btree α) : btree α → Prop
-- | empty : bst btree.empty
-- | btree : ordered (λ y _, (y < x)) l →
--           ordered (λ y _, (y > x)) r → 
--           bst l → bst r → bst (btree.node l x a r)

end btree_def