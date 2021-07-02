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

/- Definition for an empty tree -/
def empty_tree : btree α := btree.empty

/- Retrieving an item from a binary tree -/
def lookup (x : nat) : btree α → option α
| btree.empty := none
| (btree.node l k a r) :=
  if x < k then lookup l
  else if x > k then lookup r
  else a

/-
  Inserting an item into a binary tree
  If the key to insert is smaller than the current node, 
  the insertion is done recursively in the left subtree.
  If the key to insert is larger than the current node, the insertion
  is done recursively in the left subtree
-/
def insert (x : nat) (a : α) : btree α → btree α
| btree.empty := btree.node btree.empty x a btree.empty
| (btree.node l k a' r) :=
  if x < k then btree.node (insert l) k a' r
  else if x > k then btree.node l k a' (insert r)
  else btree.node l x a r

/-
  Checking if a key exists in a tree.
  For this case, there is no need to know in which subtree it is in,
  it matters that it exists in the first place
-/
def bound (x : nat) : btree α → bool
| btree.empty := ff
| (btree.node l k a r) :=
  x = k ∨ bound l ∨ bound r

/-
  An "unfolded" definition of forall_keys
  Rather than the first forall_keys definition which gives the relationship
  between the tree and the key, the unfolded definition describes the relationship between 
  the key and the child subtrees
-/
def forall_keys_unfolded (p : nat → nat → Prop) : nat → btree α → Prop
| x btree.empty := tt
| x (btree.node l k a r) :=
  forall_keys_unfolded x l ∧ (p x k) ∧ forall_keys_unfolded x r

/- For all keys in some tree, the key needs to exist in the tree and have either a > or < relation -/
def forall_keys (p : nat → nat → Prop) (k : nat) (t : btree α) : Prop :=
  ∀ k', bound k' t → p k k'

/-
  Binary search property
  For any node in a tree, all of the keys to the left must be smaller and
  all of the keys to the right must be larger, and both of the right and 
  left children must be ordered themselves
-/
def ordered : btree α → Prop
| btree.empty := tt
| (btree.node l k a r) :=
  ordered l ∧ ordered r ∧ (forall_keys (>) k l) ∧ (forall_keys (<) k r)

/-
  Definition for the height of a tree
  The height is the longest path from the root node
  To some leaf node
-/
def height : btree α → nat
| btree.empty := 0
| (btree.node l k a r) :=
  1 + (max (height l) (height r))

/-
  Definition for a tree to be balanced
-/
def balanced : btree α → bool
| btree.empty := tt
| (btree.node l k a r) :=
  if height l ≥ height r then height l ≤ height r + 1
  else height r ≤ height l + 1

/- Definition of a tree being left-heavy -/
def left_heavy : btree α → bool
| btree.empty := ff
| (btree.node btree.empty k a r) := ff
| (btree.node (btree.node ll lk la lr) k a r) :=
  (height ll ≥ height lr) ∧ (height ll ≤ height lr + 1) ∧
  (height lr ≥ height r) ∧ (height r + 1 = height ll)

/- Definition of a tree being right-heavy -/
def right_heavy : btree α → bool
| btree.empty := ff
| (btree.node l k a btree.empty) := ff
| (btree.node l k a (btree.node rl rk ra rr)) :=
  (height rr ≥ height rl) ∧ (height rr ≤ height rl + 1) ∧
  (height rl ≤ height l) ∧ (height l + 1 = height rr)

/- Simple right rotation -/
def simple_right : btree α → btree α
| btree.empty := btree.empty
| (btree.node (btree.node ll lk la lr) k a r) := btree.node ll lk la (btree.node lr k a r)
| (btree.node l k a r) := btree.node l k a r

/- Simple right rotation -/
def simple_left : btree α → btree α
| btree.empty := btree.empty
| (btree.node l k a (btree.node rl rk ra rr)) := (btree.node (btree.node l k a rl) rk ra rr)
| (btree.node l k a r) := btree.node l k a r

/-
  Definition of a right rotation
  If the left subtree is larger than the right subtree, then compound rotation is done
  Otherwise, just a simple right rotation
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

/-  Definition of a left rotation -/
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
  Works the same as insertion but checks for height differences
  and rotates as necessary.
  If insertion is done in the left subtree and this causes a disbalance, then 
  a right rotation is done.
  If insertion is done in the right subtree and this causes a disbalance, then
  a left rotation is done.
-/
def insert_balanced (x : nat) (v : α) : btree α → btree α
| btree.empty := btree.node btree.empty x v btree.empty
| (btree.node l k a r) :=
  if x < k then
    let nl := insert_balanced l in
    if height nl > height r + 1 then rotate_right (btree.node nl k a r)
    else btree.node nl k a r
  else if x > k then
    let nr := insert_balanced r in
    if height nr > height l + 1 then rotate_left (btree.node l k a nr)
    else btree.node l k a nr
  else btree.node l x v r

/- 
  "Shrinking" the right subtree of a three
  Returns a key x, which is the largest key in the right subtree, 
  the data of the node key x and the shrunken tree.
  Rotations may be done to re-balance
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

/- 
  Deleting a node from a tree
  If the left subtree is empty, the node is replaced with the right subtree
  Otherwise, the left subtree is shrunk until an empty subtree is found.
-/
def del_node : btree α → btree α
| btree.empty := btree.empty
| (btree.node l k v r) :=
  match shrink l with 
  | none := r
  | some (x, a, sh) :=
    if height r > height sh + 1 then rotate_left (node sh x a r)
    else node sh x a r
  end

/- 
  Deleting a key from a tree 
-/
def delete (x : nat) : btree α → btree α
| btree.empty := btree.empty
| (btree.node l k a r) :=
  let dl := delete l in
  let dr := delete r in
  if x = k then del_node (btree.node l k a r)
  else if x < k then
    if height r > height dl + 1 then rotate_left (btree.node dl k a r)
    else btree.node dl k a r
  else if height l > height dr + 1 then rotate_right (btree.node l k a dr)
  else (btree.node l k a dr)

/- 
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

/- 
  View inductive definition for del_node
-/
inductive del_node_view {α} : btree α → btree α → Sort*
| empty : del_node_view empty empty
| nonempty_empty : ∀ {l k v r},
  shrink l = none →
  del_node_view (node l k v r) r
| nonempty_nonempty₁ : ∀ {l k v r x a sh},
  shrink l = some (x, a, sh) →
  height r > height sh + 1 →
  del_node_view (node l k v r) (rotate_left (node sh x a r))
| nonempty_nonempty₂ : ∀ {l k v r x a sh},
  shrink l = some (x, a, sh) →
  height r ≤ height sh + 1 →
  del_node_view (node l k v r) (node sh x a r)

end btree