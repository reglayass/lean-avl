import algebra

universe u

inductive btree (α : Type u)
| empty {} : btree
| node (l : btree) (k : nat) (a : α) (r : btree) : btree

-- TODO: remove once done
def tostring : btree string → string
| btree.empty := "_"
| (btree.node l k a r) := "[" ++ " " ++ to_string k ++ " " ++ tostring l ++ " " ++ tostring r ++ " " ++ "]"

namespace btree
variables {α : Type u}

def empty_tree : btree α := btree.empty

def lookup (x : nat) : btree α → option α
| btree.empty := none
| (btree.node l k a r) := 
  if x < k then lookup l 
  else if x > k then lookup r 
  else a

def bound (x : nat) : btree α → bool
| btree.empty := ff
| (btree.node l k a r) :=
  if x < k then bound l
  else if x > k then bound r
  else tt

def insert (x : nat) (a : α) : btree α → btree α
| btree.empty := btree.node btree.empty x a btree.empty
| (btree.node l k a' r) :=
  if x < k then btree.node (insert l) k a' r
  else if x > k then btree.node l k a' (insert r)
  else btree.node l x a r

section ordering

def forall_keys (p : nat → nat → Prop) : btree α → nat → Prop
| btree.empty x := tt
| (btree.node l k a r) x := 
  forall_keys l x ∧ (p x k) ∧ forall_keys r x

def ordered : btree α → Prop
| btree.empty := tt 
| (btree.node l k a r) := 
  ordered l ∧ ordered r ∧ (forall_keys (>) l k) ∧ (forall_keys (<) r k)

end ordering

section balancing

def height : btree α → int
| btree.empty := 0
| (btree.node l k a r) :=
  1 + (max (height l) (height r))

def balanced : btree α → bool
| btree.empty := tt
| (btree.node l k a r) :=
  abs (height l - height r) ≤ 1

def outLeft : btree α → bool
| btree.empty := ff
| (btree.node l k a r) :=
  match l with
  | btree.empty := outLeft l
  | (btree.node ll lk la lr) := 
    (height ll ≥ height lr) ∧ (height ll ≤ height lr + 1) ∧ 
    (height lr ≥ height r) ∧ (height ll = height r + 1)
  end

def outRight : btree α → bool
| btree.empty := ff
| (btree.node l k a r) :=
  match r with
  | btree.empty := outRight r
  | (btree.node rl rk ra rr) :=
    (height rl ≤ height rr) ∧ (height rl ≤ height rr + 1) ∧
    (height rr ≥ height l) ∧ (height l + 1 = height rr)
  end

def easyR : btree α → btree α
| btree.empty := btree.empty
| (btree.node (btree.node ll lk la lr) k a r) := btree.node ll lk la (btree.node lr k a r)
| (btree.node l k a r) := btree.node l k a r

def easyL : btree α → btree α
| btree.empty := btree.empty
| (btree.node l k a (btree.node rl rk ra rr)) := (btree.node (btree.node l k a rl) rk ra rr)
| (btree.node l k a r) := btree.node l k a r

def rotR : btree α → btree α
| btree.empty := btree.empty
| (btree.node l k a r) :=
  match l with
  | btree.empty := (btree.node l k a r)
  | (btree.node ll lk la lr) := 
    if height ll < height lr then easyR (btree.node (easyL l) k a r)
    else easyR (btree.node l k a r)
  end

-- def rotR: btree α → btree α
-- | btree.empty := btree.empty
-- | (btree.node (btree.node ll lk la lr) k a r) :=
--   if (height ll < height lr) then easyR (btree.node (easyL (btree.node ll lk la lr)) k a r)
--   else easyR (btree.node ll k a r)
-- | (btree.node l k a r) := (btree.node l k a r)

-- def rotL : btree α → btree α
-- | btree.empty := btree.empty
-- | (btree.node l k a (btree.node rl rk ra rr)) :=
--   if (height rr < height rl) then easyL (btree.node l k a (easyR (btree.node rl rk ra rr)))
--   else easyL (btree.node l k a (btree.node rl rk ra rr))
-- | (btree.node l k a r) := btree.node l k a r

-- def insert_bal (x : nat) (a : α) : btree α → btree α
-- | btree.empty := btree.node btree.empty x a btree.empty
-- | (btree.node l k a' r) :=
--   if x < k then 
--     if (height (insert_bal l) > (height r + 1)) then rotR (btree.node (insert_bal l) k a' r) 
--     else btree.node (insert_bal l) k a' r
--   else if x > k then
--     if (height (insert_bal r) > (height l + 1)) then rotL (btree.node l k a' (insert_bal r))
--     else btree.node l k a' (insert_bal r)
--   else btree.node l x a r

end balancing

end btree