namespace treedef

/- # Search Trees -/

/--
  Inductive type: Search Tree 
  Either consists of an empty tree, or a node that 
  has a key, data, and a left and right subtree.
-/
inductive stree (α : Type) : Type
| empty {} : stree
| node (l : stree) (k : nat) (a : α) (r : stree) : stree

/--
  Definition of an empty tree
-/
def empty_tree {α : Type} : stree α :=
  stree.empty


/- # Tree Equality -/
/- 
  Formal descriptions of properties of search trees and operations on them depend on subtrees, proper
  subtrees, concepts of equality between trees, and the occurence of keys in trees 
-/

def equals {α : Type} : stree α → stree α → bool
| stree.empty stree.empty := tt
| (stree.node l k a r) stree.empty := ff
| stree.empty (stree.node l k a r) := ff
| (stree.node xl x a xr) (stree.node yl y b yr) := 
    (x = y) ∧ (equals xl yl) ∧ (equals xr yr)

def subtree_of {α : Type} (s : stree α) : stree α → stree α → bool
| stree.empty s := tt
| (stree.node l k a r) stree.empty := ff
| (stree.node xl x a xr) (stree.node yl y b yr) :=
  (equals (stree.node xl x b xr) (stree.node yl y b yr)) ∨ 
  (subtree_of (stree.node xl x b xr) yl) ∨ (subtree_of (stree.node yl y b yr) yr)

def subtree_proper {α : Type} (s : stree α) : stree α → stree α → bool
| s stree.empty := ff
| s (stree.node l k a r) := (subtree_proper s l) ∨ (subtree_proper s r) 

def contains {α : Type} (k : nat) : stree α → bool
| stree.empty := ff
| (stree.node l k a r) := (k = k) ∨ (contains l) ∨ (contains r)



/- # Ordered Subtrees -/

/- 
  A search tree is ordered if the key in each non-leaf node is greater than
  all the keys that occur in the left subtree of the node and is less than all the
  keys that occur in the right subtree. 
-/

def ordered {α : Type} : stree α → bool
| stree.empty := tt
| (stree.node l k a t) := sorry

/-
  An ordered subtree cannot contain duplicate keys
  We can define a function that extracts from a search tree a list
  containing all the data elements in a tree that are associated
  with a given key, and then to prove that the list contains
  exactly one element if the key occurs in an ordered tree. 
  If the key doesn't occur in the tree, the list is empty.
-/

def treeElems {α : Type} (x : nat) : stree α → list α
| stree.empty := []
| (stree.node l k a t) := 
  if k = x then sorry
  else sorry

end treedef