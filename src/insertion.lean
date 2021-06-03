import definitions
import rotations
import tactic.linarith
import tactic.omega
set_option pp.generalized_field_notation false

universe u

namespace insertion_balanced_lemmas
open btree
open rotation_lemmas

variables {α : Type u}

lemma forall_insert_balanced (k k' : nat) (t : btree α) (a : α) (p : nat → nat → Prop) (h : p k' k) :
  forall_keys p k' t → forall_keys p k' (insert_balanced k a t) :=
begin
  intro h₁,
  induction t,
  case empty {
    simp [insert_balanced, forall_keys],
    assumption,
  },
  case node : tl tk ta tr ihl ihr {
    simp only [insert_balanced],
    by_cases c₁ : (k < tk),
    { simp only [if_pos c₁], 
      by_cases c₂ : (height (insert_balanced k a tl) > height tr + 1),
      { simp only [if_pos c₂], 
        apply forall_rotate_right,
        { rw forall_keys at *,
          apply and.left (and.right h₁),
        },
        { rw forall_keys at *,
          cases_matching* (_ ∧ _),
          repeat { split }; try { assumption },
          apply ihl, assumption, 
        }
      },
      { simp only [if_neg c₂], 
        rw forall_keys at *,
        cases_matching* (_ ∧ _),
        repeat { split }; try { assumption },
        { apply ihl, assumption, },
      },
    },
    { simp only [if_neg c₁], 
      by_cases c₂ : (k > tk),
      { simp only [if_pos c₂], 
        by_cases c₃ : (height (insert_balanced k a tr) > height tl + 1),
        { simp only [if_pos c₃], 
          apply forall_rotate_left,
          { rw forall_keys at h₁, 
            apply and.left (and.right h₁),
          },
          { rw forall_keys at *,
            cases_matching* (_ ∧ _),
            repeat { split }; try { assumption },
            { apply ihr, assumption, },
          },
        },
        { simp only [if_neg c₃], 
          rw forall_keys at *,
          cases_matching* (_ ∧ _),
          repeat { split }; try { assumption },
          { apply ihr, assumption, },
        },
      },
      { simp only [if_neg c₂], 
        have h : tk = k := by linarith,
        subst h,
        rw forall_keys at *,
        assumption,
      },
    },
  },
end

lemma insert_ordered (t : btree α) (k : nat) (v : α) :
  ordered t → ordered (insert_balanced k v t) :=
begin
  intro h₁,
  induction t,
  case empty {
    simp only [insert_balanced, ordered],
    finish,
  },
  case node : tl tk ta tr ihl ihr {
    simp only [insert_balanced],
    by_cases c₁ : (k < tk),
    { simp only [if_pos c₁], 
      by_cases c₂ : (height (insert_balanced k v tl) > height tr + 1),
      { simp only [if_pos c₂], 
        apply rotate_right_ordered,
        rw ordered at *,
        cases_matching* (_ ∧ _),
        repeat { split }; try { assumption },
        { apply ihl, assumption, },
        { apply forall_insert_balanced; assumption, }
      },
      { simp only [if_neg c₂], 
        rw ordered at *,
        cases_matching* (_ ∧ _),
        repeat { split }; try { assumption },
        { apply ihl, assumption, },
        { apply forall_insert_balanced; assumption, },
      },
    },
    { simp only [if_neg c₁], 
      by_cases c₂ : (k > tk),
      { simp only [if_pos c₂],
        by_cases c₃ : (height (insert_balanced k v tr) > height tl + 1), 
        { simp only [if_pos c₃], 
          apply rotate_left_ordered,
          rw ordered at *,
          cases_matching* (_ ∧ _),
          repeat { split }; try { assumption },
          { apply ihr, assumption, },
          { apply forall_insert_balanced; assumption, },
        },
        { simp only [if_neg c₃], 
          rw ordered at *,
          cases_matching* (_ ∧ _),
          repeat { split }; try { assumption },
          { apply ihr, assumption, },
          { apply forall_insert_balanced; assumption, },
        },
      },
      { simp only [if_neg c₂], 
        rw ordered at *,
        have h : tk = k := by linarith,
        cases_matching* (_ ∧ _),
        repeat { split }; try { assumption },
        { subst h, assumption, },
        { subst h, assumption, },
      },
    },
  },
end

lemma insert_balanced_bound (t : btree α) (k : nat) (v : α) :
  bound k (insert_balanced k v t) :=
begin
  induction t,
  case empty {
    simp [insert_balanced, bound],
  },
  case node : tl tk ta tr ihl ihr {
    simp [insert_balanced],
    by_cases c₁ : (k < tk),
    { simp only [if_pos c₁], 
      by_cases c₂ : (height tr + 1 < height (insert_balanced k v tl)),
      { simp only [if_pos c₂], 
        apply rotate_right_keys,
        simp [bound],
        finish,
      },
      { simp only [if_neg c₂], 
        simp [bound],
        finish,
      },
    },
    { simp only [if_neg c₁], 
      by_cases c₂ : (tk < k),
      { simp only [if_pos c₂], 
        by_cases c₃ : (height tl + 1 < height (insert_balanced k v tr)),
        { simp only [if_pos c₃], 
          apply rotate_left_keys,
          simp [bound],
          finish,
        },
        { simp only [if_neg c₃], 
          simp [bound],
          finish,
        },
      },
      { simp [if_neg c₂, bound], },
    },
  }
end

end insertion_balanced_lemmas