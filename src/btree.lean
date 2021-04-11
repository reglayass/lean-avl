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

def tostring : btree string → string
| btree.empty := "_"
| (btree.node l k a r) := "[" ++ " " ++ to_string k ++ " " ++ tostring l ++ " " ++ tostring r ++ " " ++ "]"

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

def forall_keys {α : Type} (p : nat → nat → Prop) : nat → btree α → Prop
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
| (btree.node l k a r) := ordered l ∧ ordered r ∧ (forall_keys (<) k l) ∧ (forall_keys (>) k r)

end btree_def