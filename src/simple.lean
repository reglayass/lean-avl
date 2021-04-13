import basic
import tactic.linarith
set_option pp.generalized_field_notation false

universe u

namespace simple_lemmas
open btree

variables {α : Type u}

/- If we lookup empty btree then return none -/
lemma lookup_empty (k : nat) :
  lookup k (@empty_tree α) = none := by refl

/- If you check if a key is bound on an empty tree, bound will return false -/
lemma bound_empty (k : nat) :
  bound k (@empty_tree α) = ff := by refl

/- If bound returns false, then the key is not in the tree therefore
  The lookup will return none -/
lemma bound_false (k : nat) (t : btree α) :
  bound k t = ff → lookup k t = none :=
begin
  intro h₁,
  induction t,
  case empty { refl, },
  case node : tl tk ta tr ihl ihr {
    simp only [lookup],
    by_cases c₁ : (k < tk),
    { simp only [if_pos c₁], 
      rw bound at h₁,
      simp only [if_pos c₁] at h₁,
      apply ihl; assumption,
    },
    { simp only [if_neg c₁], 
      by_cases c₂ : (k > tk),
      { simp only [if_pos c₂], 
        rw bound at h₁,
        simp only [if_neg c₁, if_pos c₂] at h₁,
        apply ihr; assumption,
      },
      { simp only [if_neg c₂], 
        rw bound at h₁,
        simp only [if_neg c₁, if_neg c₂] at h₁,
        exfalso, exact h₁,
      },
    },
  },
end

lemma bound_lookup (t : btree α) (k : nat) :
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
    },
  },
end

lemma lookup_insert_eq (k : nat) (t : btree α) (v : α) :
  lookup k (insert k v t) = v :=
begin
  induction t,
  case empty {
    simp only [btree.insert, lookup],
    by_cases (k < k), 
    { exfalso, linarith },
    { simp [if_neg h] },
  },
  case node : l k' a' r ihl ihr {
    simp only [btree.insert],
    by_cases (k < k'),
    { simp only [if_pos h, lookup, ihl] },
    { simp only [if_neg h], 
      by_cases h' : (k > k'), 
      { simp only [if_pos h', lookup, if_neg h, ihr] },
      { simp only [if_neg h', lookup, if_neg (lt_irrefl k)], }
    },
  },
end

lemma lookup_insert_shadow (t : btree α) (v v' d : α) (k k' : nat) :
  lookup k' (insert k v (insert k v t)) = lookup k' (insert k v t) :=
begin
  induction t,
  case empty {
    simp only [btree.insert, lookup],
    by_cases c₁ : (k < k),
    { exfalso, linarith, },
    { simp [if_neg c₁, lookup], },
  },
  case node : tl tk ta tr ihl ihr {
    simp only [btree.insert, lookup],
    by_cases c₁ : (k < tk),
    { simp [if_pos c₁, lookup, btree.insert], 
      by_cases c₂ : (k' < tk),
      { simp [if_pos c₂], assumption, },
      { simp [if_neg c₂], }
    },
    { simp [if_neg c₁, lookup, btree.insert], 
      by_cases c₃ : (tk < k),
      { simp [if_pos c₃, btree.insert, if_neg c₁, btree.insert, lookup],
        by_cases c₄ : (k' < tk),
        { simp [if_pos c₄], },
        { simp [if_neg c₄], 
          by_cases c₅ : (tk < k'),
          { simp [if_pos c₅], assumption, },
          { simp [if_neg c₅], }
        } 
      },
      { simp [if_neg c₃, btree.insert], }
    },
  },
end

/- If you check the bound on a key just inserted into the tree, it will return false -/
lemma bound_insert_eq (k : nat) (t : btree α) (v : α) :
  bound k (insert k v t) = tt :=
begin
  induction t,
  case empty {
    simp only [btree.insert, bound],
    by_cases (k < k),
    { exfalso, linarith, },
    { simp[if_neg h], },
  },
  case node : l k' a' r ihl ihr {
    simp only [btree.insert],
    by_cases (k < k'),
    { simp only [if_pos h, btree.insert, bound, ihl], },
    { simp only [if_neg h],
      by_cases h' : (k > k'),
      { simp only [if_pos h', bound, if_neg h, ihr], },
      { simp only [if_neg h', bound, if_neg (lt_irrefl k)], } 
    },
  },
end

end simple_lemmas