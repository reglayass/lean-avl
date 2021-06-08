import definitions
import rotations
import del_node
import tactic.linarith
import tactic.induction
set_option pp.generalized_field_notation false

universe u

namespace deletion_lemmas
open btree
open rotation_lemmas
open del_node_lemmas

variables {α : Type u}

/- Deleting keys preserves order -/
lemma delete_ordered (t : btree α) (k : nat) : 
  ordered t → ordered (delete k t) :=
begin
  intro h₁,
  induction t,
  case empty {
    simp [delete, ordered],
  },
  case node : tl tk ta tr ihl ihr {
    simp only [delete],
    by_cases c₁ : (k = tk),
    { simp only [if_pos c₁], sorry },
    { simp only [if_neg c₁], 
      by_cases c₂ : (k < tk),
      { simp only [if_pos c₂], 
        by_cases c₃ : (height tr > height (delete k tl) + 1),
        { simp only [if_pos c₃], 
          apply rotate_left_ordered,
          rw ordered at *,
          cases_matching* (_ ∧ _),
          repeat { split }; try { assumption },
          { apply ihl, assumption, },
          { sorry },
        },
        { simp only [if_neg c₃], 
          rw ordered at *,
          cases_matching* (_ ∧ _),
          repeat { split }; try { assumption },
          { apply ihl, assumption },
          { sorry },
        },
      },
      { simp only [if_neg c₂], 
        by_cases c₃ : (height tl > height (delete k tr) + 1),
        { simp only [if_pos c₃], 
          apply rotate_right_ordered,
          rw ordered at *,
          cases_matching* (_ ∧ _),
          repeat { split }; try { assumption },
          { apply ihr, assumption },
          { sorry },
        },
        { simp only [if_neg c₃], 
          rw ordered at *,
          cases_matching* (_ ∧ _),
          repeat { split }; try { assumption },
          { apply ihr, assumption },
          { sorry },
        },
      },
    },
  }
end

/- Deletion does not add new keys -/
lemma delete_nbound_key (t : btree α) (k x : nat) :
  bound x t = ff → bound x (delete k t) = ff :=
begin
  intro h₁,
  induction t,
  case empty {
    simp [delete, bound],
  },
  case node : tl tk ta tr ihl ihr {
    simp only [delete],
    by_cases c₁ : (k = tk),
    { simp only [if_pos c₁],
      sorry, 
    },
    { simp only [if_neg c₁],
      by_cases c₂ : (k < tk),
      { simp only [if_pos c₂], 
        by_cases c₃ : (height tr > height (delete k tl) + 1),
        { simp only [if_pos c₃], 
          apply rotate_left_keys,
          simp [bound] at *,
          cases_matching* (_ ∧ _),
          repeat { split }; try { assumption },
          { apply ihl, assumption, },
        },
        { simp [if_neg c₃, bound] at *,
          cases_matching* (_ ∧ _),
          repeat { split }; try { assumption },
          { apply ihl, assumption, }, 
        },
      },
      { simp only [if_neg c₂], 
        by_cases c₃ : (height tl > height (delete k tr) + 1),
        { simp only [if_pos c₃], 
          apply rotate_right_keys,
          simp [bound] at *,
          cases_matching* (_ ∧ _),
          repeat { split }; try { assumption },
          { apply ihr, assumption, },
        },
        { simp [if_neg c₃, bound] at *,
          cases_matching* (_ ∧ _),
          repeat { split }; try { assumption },
          { apply ihr, assumption }, 
        },
      },
    },
  }
end

end deletion_lemmas
