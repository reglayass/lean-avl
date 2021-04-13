import tactic.linarith
set_option pp.generalized_field_notation false

namespace btree

/- # A Simple Binary tree -/

/--
  Inductive type: Binary Tree 
  Either consists of an empty tree, or a node that 
  has a key, data, and a left and right subtree.
-/
inductive btree (α: Type) : Type
| empty {} : btree
| node (l : btree) (k : nat) (a : α) (r : btree) : btree

def empty_tree {α : Type} : btree α := btree.empty

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

/- 
  If we lookup empty btree then return none -/
lemma lookup_empty {α : Type} (k : nat) : 
  lookup k (@empty_tree α) = none := 
begin
  refl,
end

/- If you check if a key is bound on an empty tree, bound will return false -/
lemma bound_empty {α : Type} (k : nat) :
  bound k (@empty_tree α) = ff :=
begin
  refl,
end

/- If bound returns false, then the key is not in the tree therefore
  The lookup will return none -/
lemma bound_false {α : Type} (k : nat) (t : btree α) :
  bound k t = ff → lookup k t = none :=
begin
  intro h₁,
  induction t,
  case empty {
    refl,
  },
  case node : l k' a r ihl ihr {
    simp only [lookup],
    by_cases (k < k'),
    { simp only [if_pos h], 
      rw bound at h₁,
      simp only [if_pos h] at h₁, apply ihl, assumption, },
    { simp only [if_neg h],
      by_cases h' : (k > k'),
      { simp only [if_pos h'],
      rw bound at h₁, simp only [if_neg h, if_pos h'] at h₁, apply ihr, assumption, }, 
      { simp only [if_neg h'], rw bound at h₁, 
        simp only [if_neg h, if_neg h'] at h₁, exfalso, apply h₁, }
    }
  }
end

lemma bound_lookup {α : Type} (t : btree α) (k : nat) :
  bound k t → ∃ (v : α), lookup k t = some v :=
begin
  intros h₁,
  induction t,
  case empty {
    simp only [lookup],
    simp [bound] at h₁,
    contradiction,
  },
  case node : tl tk ta tr ihl ihr {
    simp only [lookup],
    by_cases c₁ : (k < tk),
    { simp only [if_pos c₁],
      apply ihl,
      simp only [bound, if_pos c₁] at h₁, 
      finish,
    },
    { simp only [if_neg c₁], 
      by_cases c₂ : (k > tk),
      { simp only [if_pos c₂],
        apply ihr,
        simp only [bound, if_pos c₂, if_neg c₁] at h₁,
        finish, 
      },
      { simp only [if_neg c₂], 
        existsi ta,
        refl,
      },
    }
  }
end

/- # Inserting intro a binary tree -/

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

/-
  If we lookup the same key that we just inserted, we should get the value
  inserted with it: 
  __lookup d k (insert k v t ) = v__
-/
lemma lookup_insert_eq {α: Type} (k : nat) (t : btree α) (v : α) :
  lookup k (insert k v t) = v :=
begin
  induction t,
  case empty {
    simp only [insert, lookup],
    by_cases (k < k), 
    { exfalso, linarith },
    { simp [if_neg h] },
  },
  case node : l k' a' r ihl ihr {
    simp only [insert],
    by_cases (k < k'),
    { simp only [if_pos h, lookup, ihl] },
    { simp only [if_neg h], 
      by_cases h' : (k > k'), 
      { simp only [if_pos h', lookup, if_neg h, ihr] },
      { simp only [if_neg h', lookup, if_neg (lt_irrefl k)], }
    },
  },
end

lemma lookup_insert_shadow {α : Type} (t : btree α) (v v' d : α) (k k' : nat) :
  lookup k' (insert k v (insert k v t)) = lookup k' (insert k v t) :=
begin 
  induction t,
  case empty {
    simp only [insert, lookup],
    by_cases (k < k),
    { exfalso, linarith },
    { simp [if_neg h, lookup] }
  },
  case node : tl tk a' tr ihl ihr {
    simp only [insert, lookup],
    by_cases h₁ : (k < tk),
    { simp [if_pos h₁, insert, lookup],
      by_cases h₂ : (k' < tk),
      { simp [if_pos h₂], assumption, },
      { simp [if_neg h₂], } },
    { simp [if_neg h₁, insert, lookup],
      by_cases h₃ : (tk < k),
      { simp [if_pos h₃, insert, if_neg h₁, insert, lookup],
        by_cases h₄ : (k' < tk),
        { simp [if_pos h₄], },
        { simp [if_neg h₄],
          by_cases h₅ : (tk < k'),
          { simp [if_pos h₅], assumption },
          { simp [if_neg h₅] } } },
      { simp [if_neg h₃, insert] } } },
end

/- If you check the bound on a key just inserted into the tree, it will return false -/
lemma bound_insert_eq {α : Type} (k : nat) (t : btree α) (v : α) :
  bound k (insert k v t) = tt :=
begin
  induction t,
  case empty {
    simp only [insert, bound],
    by_cases (k < k),
    { exfalso, linarith },
    { simp[if_neg h] },
  },
  case node : l k' a' r ihl ihr {
    simp only [insert],
    by_cases (k < k'),
    { simp only [if_pos h, insert, bound, ihl] },
    { simp only [if_neg h],
      by_cases h' : (k > k'),
      { simp only [if_pos h', bound, if_neg h, ihr] },
      { simp only [if_neg h', bound, if_neg (lt_irrefl k)] } 
    }
  }
end

end btree