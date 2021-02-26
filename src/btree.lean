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



/- # Binary Search Tree Invariant -/

/-- 
Definition the BST invariant:
1. An empty btree is a BST
2. A non-empty btree is a BST if all its left nodes have a lesser key,
  its right nodes have a greater key, and the left and right subtrees 
  are themselves BSTs. 
-/
def bst_inv {α: Type} (p : nat → α → Prop) : btree α → Prop
| btree.empty := tt
| (btree.node l k a r) := (p k a) ∧ (bst_inv l) ∧ (bst_inv r)

inductive bst (α : Type) (l : btree α) (x : nat) (v : α) (r : btree α) : btree α → Prop
| empty : bst btree.empty
| btree : bst_inv (λ y _, (y < x)) l → 
          bst_inv (λ y _, (y > x)) r →
          bst l → bst r → bst (btree.node l x v r)

end btree_def