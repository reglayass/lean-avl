import practice.tree

namespace bst_invariant
open simple_tree

/-
the implementations of __lookup__ and __invariant__ assume
that all values of type __tree__ obey the BST invariant: for any 
non-empty node with key k, all the values of the left subtree are less than k
and all the values of the right subtree are greater than k. 
But that invariant is not part of the definition of __tree__
-/

-- this helper expresses the idea that a predicate
-- holds at every node of a btree
def forallt {α: Type} (p : nat → α → Prop) : btree α → Prop
| btree.empty := tt
| (btree.node l k a r) := (p k a) ∧ (forallt l) ∧ (forallt r)

/-
definition the BST invariant:
1. An empty btree is a BST
2. A non-empty btree is a BST if all its left nodes have a lesser key,
  its right nodes have a greater key, and the left and right subtrees 
  are themselves BSTs. 
-/

inductive bst {α : Type} (l : btree α) (x : nat) (v : α) (r : btree α): btree α → Prop
| empty : bst btree.empty
| btree : 
  forallt (λ y _, (y < x)) l →
  forallt (λ y _, (y > x)) r → 
  bst l → 
  bst r → 
  bst (btree.node l x v r)


lemma forallt_insert {α : Type} (t' : nat → α → Prop) (t : btree α) (k : nat) (v: α) :
  t' k v → forallt t' (insert k v t) :=
sorry

-- Theorem insert_BST : ∀ (V : Type) (k : key) (v : V) (t : tree V),
--     BST t → BST (insert k v t).
-- Proof.
--   (* FILL IN HERE *) Admitted.

end bst_invariant

namespace bst_correctness
open bst_invariant
open simple_tree

/- 
  If we lookup empty btree then return none
-/
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
    simp only [simple_tree.insert, lookup],
    by_cases (k < k), 
    { exfalso, linarith },
    { simp [if_neg h] },
  },
  case node : l k' a' r ihl ihr {
    simp only [simple_tree.insert],
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
    simp only [simple_tree.insert, lookup],
    by_cases (k < k),
    { exfalso, linarith },
    { simp [if_neg h, lookup] },
  },
  sorry
end

/- If you check the bound on a key just inserted into the tree, it will return false -/
lemma bound_insert_eq {α : Type} (k : nat) (t : btree α) (v : α) :
  bound k (insert k v t) = tt :=
begin
  induction t,
  case empty {
    simp only [simple_tree.insert, bound],
    by_cases (k < k),
    { exfalso, linarith },
    { simp[if_neg h] },
  },
  case node : l k' a' r ihl ihr {
    simp only [simple_tree.insert],
    by_cases (k < k'),
    { simp only [if_pos h, simple_tree.insert, bound, ihl] },
    { simp only [if_neg h],
      by_cases h' : (k > k'),
      { simp only [if_pos h', bound, if_neg h, ihr] },
      { simp only [if_neg h', bound, if_neg (lt_irrefl k)] } 
    }
  }
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
    { simp only [if_pos h], sorry },
    { simp only [if_neg h],
      by_cases h' : (k > k'),
      { simp only [if_pos h'], sorry }, 
      { simp only [if_neg h'], sorry }
    }
  }
end


end bst_correctness