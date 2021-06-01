import definitions
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
  case empty {
    refl,
  },
  case node : tl tk ta tr ihl ihr {
    simp [lookup],
    simp [bound] at h₁,
    by_cases c₁ : (k < tk),
    { simp [if_pos c₁], 
      apply ihl; apply and.left (and.right h₁),
    },
    { simp [if_neg c₁],
      by_cases c₂ : (tk < k),
      { simp [if_pos c₂],
        apply ihr; apply and.right (and.right h₁),
      },
      { simp [if_neg c₂],
        sorry,
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
    simp [bound] at h₁,
    by_cases c₁ : (k < tk),
    { simp only [if_pos c₁],
      apply ihl,
      sorry,
    },
    { simp only [if_neg c₁], 
      by_cases c₂ : (k > tk),
      { simp only [if_pos c₂], 
        apply ihr,
        sorry,
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

/- If you check the bound on a key just inserted into the tree, it will return true -/
lemma bound_insert_eq (k : nat) (t : btree α) (v : α) :
  bound k (insert k v t) = tt :=
begin
  induction t,
  case empty {
    simp [btree.insert, bound],
  },
  case node : tl tk ta tr ihl ihr {
    simp only [btree.insert],
    by_cases c₁ : (k < tk),
    { simp [if_pos c₁, bound],
      apply or.inr (or.inl ihl), },
    { simp [if_neg c₁], 
      by_cases c₂ : (tk < k),
      { simp [if_pos c₂, bound], 
        apply or.inr (or.inr ihr), },
      { simp [if_neg c₂, bound], },
    },
  },
end

end simple_lemmas