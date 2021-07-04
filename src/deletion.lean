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

lemma forall_keys_delete (t : btree α) (k x : nat) (p : nat → nat → Prop) (h : p k x) :
  forall_keys p k t → forall_keys p k (delete x t) :=
begin
  intro h₁,
  induction t,
  case empty {
    simp [delete],
    exact h₁,
  },
  case node : tl tk ta tr ihl ihr {
    simp [delete],
    by_cases c₁ : (x = tk),
    { simp only [if_pos c₁], 
      apply forall_del_node,
      assumption,
    },
    { simp only [if_neg c₁],
      rw forall_keys at h₁,
      by_cases c₂ : (x < tk),
      { simp only [if_pos c₂], 
        cases_matching* (_ ∧ _),
        by_cases c₃ : (height (delete x tl) + 1 < height tr),
        { simp only [if_pos c₃], 
          apply forall_rotate_left,
          { rw forall_keys, 
            sorry,
          },
        },
        { simp only [if_neg c₃], 
          rw forall_keys,
          repeat { split }; try { assumption },
          { sorry, },
        },
      },
      { simp only [if_neg c₂], 
        cases_matching* (_ ∧ _), 
        by_cases c₃ : (height (delete x tr) + 1 < height tl),
        { simp only [if_pos c₃], 
          apply forall_rotate_right,
          { rw forall_keys, 
            repeat { split }; try { assumption },
            { sorry, },
          },
        },
        { simp only [if_neg c₃], 
          rw forall_keys,
          repeat { split }; try { assumption },
          { sorry, },
        },
      },
    },
  },
end

lemma delete_ordered (t : btree α) (k : nat) :
  ordered t → ordered (delete k t) :=
begin
  intro h₁,
  induction t,
  case empty {
    simp [delete, ordered],
  },
  case node : tl tk ta tr ihl ihr {
    simp [delete],
    by_cases c₁ : (k = tk),
    { simp only [if_pos c₁],
      apply del_node_ordered,
      assumption,
    },
    { simp only [if_neg c₁], 
      by_cases c₂ : (k < tk),
      { simp only [if_pos c₂], 
        by_cases c₃ : (height (delete k tl) + 1 < height tr),
        { simp only [if_pos c₃], 
          apply rotate_left_ordered,
          rw ordered at *,
          cases_matching* (_ ∧ _),
          repeat { split }; try { assumption },
          { apply ihl, assumption, },
          { apply forall_keys_delete; assumption, },
        },
        { simp only [if_neg c₃], 
          rw ordered at *,
          cases_matching* (_ ∧ _),
          repeat { split }; try { assumption },
          { apply ihl, assumption, },
          { apply forall_keys_delete; assumption, },
        },
      },
      { simp only [if_neg c₂], 
        by_cases c₃ : (height (delete k tr) + 1 < height tl),
        { simp only [if_pos c₃], 
          apply rotate_right_ordered,
          rw ordered at *,
          cases_matching* (_ ∧ _),
          repeat { split }; try { assumption },
          { apply ihr, assumption, },
          { apply forall_keys_delete, 
            { omega, },
            { assumption, },
          },
        },
        { simp only [if_neg c₃],
          rw ordered at *,
          cases_matching* (_ ∧ _),
          repeat { split }; try { assumption },
          { apply ihr, assumption, }, 
          { apply forall_keys_delete, 
            { omega, },
            { assumption, },
          },
        },
      },
    },
  },
end

end deletion_lemmas