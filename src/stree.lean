namespace treedef

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

end treedef