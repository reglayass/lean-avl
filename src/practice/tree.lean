import tactic.linarith
set_option pp.generalized_field_notation false

namespace simple_tree

inductive btree (α : Type) : Type
| empty {} : btree
| node (l : btree) (k : nat) (a : α) (r : btree) : btree

def empty_tree {α : Type} : btree α :=
  btree.empty

def lookup {α : Type} (x : nat) : btree α → option α
| btree.empty := none
| (btree.node l k a r) := 
  if x < k then lookup l
  else if x > k then lookup r
  else a

def bound {α : Type} (x : nat) : btree α → bool
| btree.empty := ff
| (btree.node l k a r) :=
  if x < k then bound l
  else if x > k then bound r
  else tt

def insert {α : Type} (x : nat) (a : α) : btree α → btree α
| btree.empty := btree.node btree.empty x a btree.empty
| (btree.node l k a' r) :=
  if x < k then btree.node (insert l) k a' r
  else if x > k then btree.node l k a' (insert r)
  else btree.node l x a r

end simple_tree