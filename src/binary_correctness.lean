import btree
import tactic.linarith
set_option pp.generalized_field_notation false

namespace bin_correct
open btree_def

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
    simp only [btree_def.insert, lookup],
    by_cases (k < k), 
    { exfalso, linarith },
    { simp [if_neg h] },
  },
  case node : l k' a' r ihl ihr {
    simp only [btree_def.insert],
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
    simp only [btree_def.insert, lookup],
    by_cases (k < k),
    { exfalso, linarith },
    { simp [if_neg h, lookup] }
  },
  case node : tl tk a' tr ihl ihr {
    simp only [btree_def.insert, lookup],
    by_cases h₁ : (k < tk),
    { simp [if_pos h₁, btree_def.insert, lookup],
      by_cases h₂ : (k' < tk),
      { simp [if_pos h₂], assumption, },
      { simp [if_neg h₂], } },
    { simp [if_neg h₁, btree_def.insert, lookup],
      by_cases h₃ : (tk < k),
      { simp [if_pos h₃, btree_def.insert, if_neg h₁, btree_def.insert, lookup],
        by_cases h₄ : (k' < tk),
        { simp [if_pos h₄], },
        { simp [if_neg h₄],
          by_cases h₅ : (tk < k'),
          { simp [if_pos h₅], assumption },
          { simp [if_neg h₅] } } },
      { simp [if_neg h₃, btree_def.insert] } } },
end

/- If you check the bound on a key just inserted into the tree, it will return false -/
lemma bound_insert_eq {α : Type} (k : nat) (t : btree α) (v : α) :
  bound k (insert k v t) = tt :=
begin
  induction t,
  case empty {
    simp only [btree_def.insert, bound],
    by_cases (k < k),
    { exfalso, linarith },
    { simp[if_neg h] },
  },
  case node : l k' a' r ihl ihr {
    simp only [btree_def.insert],
    by_cases (k < k'),
    { simp only [if_pos h, btree_def.insert, bound, ihl] },
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

end bin_correct