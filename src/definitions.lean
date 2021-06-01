universe u

set_option pp.generalized_field_notation false

inductive btree (α : Type u)
| empty {} : btree
| node (l : btree) (k : nat) (a : α) (r : btree) : btree

namespace btree
variables {α : Type u}

def empty_tree : btree α := btree.empty

def lookup (x : nat) : btree α → option α
| btree.empty := none
| (btree.node l k a r) :=
  if x < k then lookup l
  else if x > k then lookup r
  else a

def insert (x : nat) (a : α) : btree α → btree α
| btree.empty := btree.node btree.empty x a btree.empty
| (btree.node l k a' r) :=
  if x < k then btree.node (insert l) k a' r
  else if x > k then btree.node l k a' (insert r)
  else btree.node l x a r

def bound (x : nat) : btree α → bool
| btree.empty := ff
| (btree.node l k a r) :=
  x = k ∨ bound l ∨ bound r

def forall_keys (p : nat → nat → Prop) : nat → btree α → Prop
| x btree.empty := tt
| x (btree.node l k a r) :=
  forall_keys x l ∧ (p x k) ∧ forall_keys x r

def ordered : btree α → Prop
| btree.empty := tt
| (btree.node l k a r) :=
  ordered l ∧ ordered r ∧ (forall_keys (>) k l) ∧ (forall_keys (<) k r)

def height : btree α → nat
| btree.empty := 0
| (btree.node l k a r) :=
  1 + (max (height l) (height r))

def balanced : btree α → bool
| btree.empty := tt
| (btree.node l k a r) :=
  if height l ≥ height r then height l ≤ height r + 1
  else height r ≤ height l + 1

def left_heavy : btree α → bool
| btree.empty := ff
| (btree.node l k a r) :=
  match l with
  | btree.empty := ff
  | (btree.node ll lk la lr) :=
    (height ll ≥ height lr) ∧ (height ll ≤ height lr + 1) ∧
    (height lr ≥ height r) ∧ (height r + 1 = height ll)
  end

def right_heavy : btree α → bool
| btree.empty := ff
| (btree.node l k a r) :=
  match r with
  | btree.empty := ff
  | (btree.node rl rk ra rr) :=
    (height rr ≥ height rl) ∧ (height rr ≤ height rl + 1) ∧
    (height rl ≤ height l) ∧ (height l + 1 = height rr)
  end

def simple_right : btree α → btree α
| btree.empty := btree.empty
| (btree.node (btree.node ll lk la lr) k a r) := btree.node ll lk la (btree.node lr k a r)
| (btree.node l k a r) := btree.node l k a r

def simple_left : btree α → btree α
| btree.empty := btree.empty
| (btree.node l k a (btree.node rl rk ra rr)) := (btree.node (btree.node l k a rl) rk ra rr)
| (btree.node l k a r) := btree.node l k a r

def rotate_right : btree α → btree α
| btree.empty := btree.empty
| (btree.node l k a r) :=
  match l with
  | btree.empty := (btree.node l k a r)
  | (btree.node ll lk la lr) :=
    if height ll < height lr then simple_right (btree.node (simple_left l) k a r)
    else simple_right (btree.node l k a r)
  end 

def rotate_left : btree α → btree α
| btree.empty := btree.empty
| (btree.node l k a r) :=
  match r with
  | btree.empty := (btree.node l k a r)
  | (btree.node rl rk ra rr) :=
    if height rr < height rl then simple_left (btree.node l k a (simple_right r))
    else simple_left (btree.node l k a r)
  end

def balance : btree α → btree α
| btree.empty := btree.empty
| (btree.node l k a r) :=
  if left_heavy (btree.node l k a r) then rotate_right (btree.node (balance l) k a r)
  else if right_heavy (btree.node l k a r) then rotate_left (btree.node l k a (balance r))
  else btree.node l k a r

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

def inorder_pred : btree α → option (nat × α × btree α)
| btree.empty := none
| (btree.node l k v r) := some $
  match inorder_pred r with
  | none := (k, v, l)
  | some (x, a, sh) :=
    if height l > height sh + 1
      then (x, a, rotate_right (btree.node l k v sh))
      else (x, a, btree.node l k v sh)
  end

def del_node : btree α → btree α
| btree.empty := btree.empty
| (btree.node l k v r) :=
  match inorder_pred l with 
  | none := r
  | some (x, a, sh) :=
    if height r > height sh + 1 then rotate_left (node sh x a r)
    else node sh x a r
  end

inductive inorder_pred_view {α} : btree α → option (nat × α × btree α) → Sort*
| empty : inorder_pred_view empty none
| nonempty_empty : ∀ {l k v r},
  inorder_pred r = none →
  inorder_pred_view (node l k v r) (some (k, v, l))
| nonempty_nonempty₁ : ∀ {l k v r x a sh out},
  inorder_pred r = some (x, a, sh) →
  height l > height sh + 1 →
  out = some (x, a, rotate_right (btree.node l k v sh)) →
  inorder_pred_view (node l k v r) out
| nonempty_nonempty₂ : ∀ {l k v r x a sh},
  inorder_pred r = some (x, a, sh) →
  height l ≤ height sh + 1 →
  inorder_pred_view (node l k v r) (some (x, a, node l k v sh))

/- delRoot_view t dt ↔ delRoot t = dt -/
inductive del_node_view {α} : btree α → btree α → Sort*
| empty : del_node_view empty empty
| nonempty_empty : ∀ {l k v r},
  inorder_pred l = none →
  del_node_view (node l k v r) r
| nonempty_nonempty₁ : ∀ {l k v r x a sh},
  inorder_pred l = some (x, a, sh) →
  height r > height sh + 1 →
  del_node_view (node l k v r) (rotate_left (node sh x a r))
| nonempty_nonempty₂ : ∀ {l k v r x a sh},
  inorder_pred l = some (x, a, sh) →
  height r ≤ height sh + 1 →
  del_node_view (node l k v r) (node sh x a r)

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

end btree
