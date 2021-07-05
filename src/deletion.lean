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
    simp only [delete],
    by_cases c₁ : (k = tk),
    { simp only [if_pos c₁], 
      apply del_node_ordered,
      exact h₁,
    },
    { simp only [if_neg c₁],
      rw ordered at h₁,
      cases_matching* (_ ∧ _),
      by_cases c₂ : (k < tk),
      { simp only [if_pos c₂], 
        by_cases c₃ : (height (delete k tl) + 1 < height tr),
        { simp only [if_pos c₃], 
          apply rotate_left_ordered,
          repeat { split }; try { assumption },
          { apply ihl, assumption, },
          { apply forall_keys_delete; assumption, },
        },
        { simp only [if_neg c₃], 
          repeat { split }; try { assumption },
          { apply ihl, assumption, },
          { apply forall_keys_delete; assumption, },
        }, 
      },
      { simp only [if_neg c₂], 
        by_cases c₃ : (height tl > height (delete k tr) + 1),
        { simp only [if_pos c₃], 
          apply rotate_right_ordered,
          repeat { split }; try { assumption },
          { apply ihr, assumption, },
          { apply forall_keys_delete, 
            { omega, },
            { assumption, },
          },
        },
        { simp only [if_neg c₃], 
          repeat { split }; try { assumption },
          { apply ihr, assumption, },
          { apply forall_keys_delete, 
            { omega, },
            { assumption, },
          }
        },
      },
    },
  },
end

end deletion_lemmas