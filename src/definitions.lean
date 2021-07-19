universe u 

/--
  Inductive type for a binary tree
  A tree can either be empty, or have two children (which may also be empty)
  A tree node contains a key and a node value
-/
inductive btree (α : Type u)
| empty {} : btree
| node (l : btree) (k : nat) (a : α) (r : btree) : btree

namespace btree
variables {α : Type u}

/--
 Definition for an empty tree 
-/
def empty_tree : btree α := btree.empty

/--
  Lookup a value in a tree
  A recursive function that traverses the left or right
  subtree depending on the key
-/
def lookup (x : nat) : btree α → option α
| btree.empty := none
| (btree.node l k a r) :=
  if x < k 
    then lookup l
    else if x > k 
      then lookup r
    else a

/-
  Checking if a key exists in a tree.
  For this case, there is no need to know in which subtree it is in,
  it matters that it exists in the first place
-/
def bound (x : nat) : btree α → bool
| btree.empty := ff
| (btree.node l k a r) :=
  x = k ∨ bound l ∨ bound r

/--
  For all keys in some tree, the key needs to exist in the tree and have either a > or < relation 
-/
def forall_keys (p : nat → nat → Prop) (k : nat) (t : btree α) : Prop :=
  ∀ k', bound k' t → p k k'

/--
  Binary search property
  For any node in a tree, all of the keys to the left must be smaller and
  all of the keys to the right must be larger, and both of the right and 
  left children must be ordered themselves
-/
def ordered : btree α → Prop
| btree.empty := tt
| (btree.node l k a r) :=
  ordered l ∧ ordered r ∧ (forall_keys (>) k l) ∧ (forall_keys (<) k r)

/--
  Definition for the height of a tree
  The height is the longest path from the root node
  To some leaf node
-/
def height : btree α → nat
| btree.empty := 0
| (btree.node l k a r) :=
  1 + (max (height l) (height r))

/--
  Definition for a tree to be balanced
-/
def balanced : btree α → bool
| btree.empty := tt
| (btree.node l k a r) :=
  if height l ≥ height r 
    then height l ≤ height r + 1
    else height r ≤ height l + 1

/-- 
  Definition of a tree being left-heavy 
-/
def left_heavy : btree α → bool
| btree.empty := ff
| (btree.node btree.empty k a r) := ff
| (btree.node (btree.node ll lk la lr) k a r) :=
  (height ll ≥ height lr) ∧ (height ll ≤ height lr + 1) ∧
  (height lr ≥ height r) ∧ (height r + 1 = height ll)

/-- 
  Definition of a tree being right-heavy 
-/
def right_heavy : btree α → bool
| btree.empty := ff
| (btree.node l k a btree.empty) := ff
| (btree.node l k a (btree.node rl rk ra rr)) :=
  (height rr ≥ height rl) ∧ (height rr ≤ height rl + 1) ∧
  (height rl ≤ height l) ∧ (height l + 1 = height rr)

/-- 
  Simple right rotation 
-/
def simple_right : btree α → btree α
| btree.empty := btree.empty
| (btree.node (btree.node ll lk la lr) k a r) := btree.node ll lk la (btree.node lr k a r)
| (btree.node l k a r) := btree.node l k a r

/-- 
  Simple left rotation 
-/
def simple_left : btree α → btree α
| btree.empty := btree.empty
| (btree.node l k a (btree.node rl rk ra rr)) := (btree.node (btree.node l k a rl) rk ra rr)
| (btree.node l k a r) := btree.node l k a r

/--
  Definition of a right rotation
  If the left child tree is empty, no rotation is done
  If the left child subtree is taller than the right child subtree, 
  a compound rotation is done by first a left rotation on the left tree 
  then a right rotation on the whole tree. 
  Otherwise, a simple right rotation is done.
-/
def rotate_right : btree α → btree α
| btree.empty := btree.empty
| (btree.node l k a r) :=
  match l with
  | btree.empty := (btree.node l k a r)
  | (btree.node ll lk la lr) :=
    if height ll < height lr 
      then simple_right (btree.node (simple_left l) k a r)
      else simple_right (btree.node l k a r)
  end 

/--  
  Definition of a left rotation 
  A mirror definition to rotate_right
-/
def rotate_left : btree α → btree α
| btree.empty := btree.empty
| (btree.node l k a r) :=
  match r with
  | btree.empty := (btree.node l k a r)
  | (btree.node rl rk ra rr) :=
    if height rr < height rl 
      then simple_left (btree.node l k a (simple_right r))
      else simple_left (btree.node l k a r)
  end

/- 
  Definition of a balanced insertion
  Traverses the tree by comparing keys similar to lookup.
  If the tree is left- or right-heavy after insertion, a rotation
  is done.   
-/
def insert (x : nat) (v : α) : btree α → btree α
| btree.empty := btree.node btree.empty x v btree.empty
| (btree.node l k a r) :=
  if x < k 
    then if left_heavy (btree.node (insert l) k a r) 
      then rotate_right (btree.node (insert l) k a r)
      else btree.node (insert l) k a r
    else if x > k 
      then if right_heavy (btree.node l k a (insert r)) 
        then rotate_left (btree.node l k a (insert r))
        else btree.node l k a (insert r)
    else btree.node l x v r

/- 
  "Shrinking" the right subtree of a three
  Returns x, which the key of the node in r with an empty right subtree
  Return a, which is the node value the node with key x
  Returns sh, the "shrunken" tree 
-/
def shrink : btree α → option (nat × α × btree α)
| btree.empty := none
| (btree.node l k v r) := some $
  match shrink r with
  | none := (k, v, l)
  | some (x, a, sh) :=
    if height l > height sh + 1
      then (x, a, rotate_right (btree.node l k v sh))
      else (x, a, btree.node l k v sh)
  end

/-- 
  Deleting the root of a tree
  If the left subtree is empty, the node is replaced with the right subtree
  Otherwise, the left subtree is shrunk until an empty subtree is found.
-/
def del_root : btree α → btree α
| btree.empty := btree.empty
| (btree.node l k v r) :=
  match shrink l with 
  | none := r
  | some (x, a, sh) :=
    if height r > height sh + 1 
      then rotate_left (node sh x a r)
      else node sh x a r
  end

/-- 
  Deleting a key from a tree 
  If the input key is the same as the current node key, 
  the node is deleted
  Otherwise deletion is recursively called on either the right or left subtree,
  rotations completed as necessary.
-/
def delete (x : nat) : btree α → btree α
| btree.empty := btree.empty
| (btree.node l k a r) :=
  let dl := delete l in
  let dr := delete r in
  if x = k 
    then del_root (btree.node l k a r)
    else if x < k 
      then if height r > height dl + 1 
        then rotate_left (btree.node dl k a r)
        else btree.node dl k a r
    else if height l > height dr + 1 
      then rotate_right (btree.node l k a dr)
    else (btree.node l k a dr)

/-- 
  View inductive definition for shrink
-/
inductive shrink_view {α} : btree α → option (nat × α × btree α) → Sort*
| empty : shrink_view empty none
| nonempty_empty : ∀ {l k v r},
  shrink r = none →
  shrink_view (node l k v r) (some (k, v, l))
| nonempty_nonempty₁ : ∀ {l k v r x a sh out},
  shrink r = some (x, a, sh) →
  height l > height sh + 1 →
  out = some (x, a, rotate_right (btree.node l k v sh)) →
  shrink_view (node l k v r) out
| nonempty_nonempty₂ : ∀ {l k v r x a sh},
  shrink r = some (x, a, sh) →
  height l ≤ height sh + 1 →
  shrink_view (node l k v r) (some (x, a, node l k v sh))

/-- 
  View inductive definition for del_node
-/
inductive del_root_view {α} : btree α → btree α → Sort*
| empty : del_root_view empty empty
| nonempty_empty : ∀ {l k v r},
  shrink l = none →
  del_root_view (node l k v r) r
| nonempty_nonempty₁ : ∀ {l k v r x a sh},
  shrink l = some (x, a, sh) →
  height r > height sh + 1 →
  del_root_view (node l k v r) (rotate_left (node sh x a r))
| nonempty_nonempty₂ : ∀ {l k v r x a sh},
  shrink l = some (x, a, sh) →
  height r ≤ height sh + 1 →
  del_root_view (node l k v r) (node sh x a r)

end btree