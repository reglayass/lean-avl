import definitions
import tactic.linarith
import tactic.omega
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

/- If you insert into an empty tree, then you just have one node -/
lemma insert_empty (k : nat) (v : α) :
  insert k v (@empty_tree α) = btree.node btree.empty k v btree.empty := by refl

/- If bound returns false, then the key is not in the tree therefore
  The lookup will return none -/
lemma bound_false (k : nat) (t : btree α) :
  bound k t = ff → lookup k t = none :=
begin
  intro h₁,
  induction t,
  case empty {
    apply refl,
  },
  case node : tl tk ta tr ihl ihr {
    simp [lookup],
    simp [bound] at h₁,
    by_cases c₁ : (k < tk),
    { simp only [if_pos c₁], 
      apply ihl,
      apply and.left (and.right h₁),
    },
    { simp only [if_neg c₁], 
      by_cases c₂ : (tk < k),
      { simp only [if_pos c₂], 
        apply ihr,
        apply and.right (and.right h₁),
      },
      { simp only [if_neg c₂],
        cases_matching* (_ ∧ _),
        have h : k = tk := by linarith,
        have h₂ : k ≠ tk := by omega,
        contradiction,
      },
    },
  },
end

/- If a key is bound to a tree, then lookup will in result in some result -/
lemma bound_lookup (t : btree α) (k : nat) :
  bound k t = tt → ∃ (v : α), lookup k t = some v :=
begin
  intros h₁,
  induction t,
  case empty {
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

/- If you lookup a key just inserted, the same value you just inserted will be returned -/
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

end simple_lemmas