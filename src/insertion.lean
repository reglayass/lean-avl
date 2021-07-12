import definitions rotations forall_keys tactic.linarith tactic.omega
set_option pp.generalized_field_notation false

universe u

namespace insertion_balanced_lemmas
open btree rotation_lemmas forall_keys_lemmas

variables {α : Type u}

lemma forall_insert (k x : nat) (t : btree α) (a : α) (p : nat → nat → Prop) (h : p x k) :
  forall_keys p x t → forall_keys p x (insert k a t) :=
begin
  intro h₁,
  induction t,
  case empty {
    unfold forall_keys,
    intros k' h₂,
    simp [btree.insert, bound] at h₂,
    subst h₂,
    exact h,
  },
  case node : tl tk ta tr ihl ihr {
    unfold forall_keys at ihl ihr h₁,
    simp only [btree.insert],
    by_cases c₁ : (k < tk),
    { simp only [if_pos c₁], 
      by_cases c₂: ↥(left_heavy (insert k a tl)),
      { simp only [if_pos c₂], 
        apply forall_rotate_right,
        rw ← forall_keys_intro,
        unfold forall_keys,
        repeat { split },
        { apply ihl, 
          intros k' h₂,
          apply h₁,
          simp [bound],
          tauto,
        },
        { apply h₁, 
          simp [bound],
        },
        { intros k' h₂, 
          apply h₁,
          simp [bound],
          tauto,
        },
      },
      { simp only [if_neg c₂],
        rw ← forall_keys_intro,
        unfold forall_keys,
        repeat { split },
        { apply ihl, 
          intros k' h₂,
          apply h₁,
          simp [bound],
          tauto,
        },
        { apply h₁, 
          simp [bound],
        },
        { intros k' h₂, 
          apply h₁,
          simp [bound],
          tauto,
        }, 
      },
    },
    { simp only [if_neg c₁], 
      by_cases c₂ : (k > tk),
      { simp only [if_pos c₂], 
        by_cases c₃ : ↥(right_heavy (insert k a tr)),
        { simp only [if_pos c₃], 
          apply forall_rotate_left,
          rw ← forall_keys_intro,
          unfold forall_keys,
          repeat { split },
          { intros k' h₂,
            apply h₁,
            simp [bound],
            tauto, 
          },
          { apply h₁,
            simp [bound], 
          },
          { apply ihr, 
            intros k' h₂,
            apply h₁,
            simp [bound],
            tauto,
          },
        },
        { simp only [if_neg c₃],
          rw ← forall_keys_intro,
          unfold forall_keys,
          repeat { split },
          { intros k' h₂, 
            apply h₁,
            simp [bound],
            tauto,
          },
          { apply h₁, 
            simp [bound],
          },
          { apply ihr, 
            intros k' h₂,
            apply h₁,
            simp [bound],
            tauto,
          }, 
        },
      },
      { simp only [if_neg c₂], 
        have h : k = tk := by linarith,
        subst h,
        exact h₁,
      },
    },
  },
end

lemma insert_ordered (t : btree α) (k : nat) (v : α) :
  ordered t → ordered (insert k v t) :=
begin
  intro h₁,
  induction t,
  case empty {
    simp [btree.insert, ordered, forall_keys],
    split,
    { intros k' h₂, 
      simp [bound] at h₂,
      contradiction,
    },
    { intros k' h₂, 
      simp [bound] at h₂,
      contradiction,
    },
  },
  case node : tl tk ta tr ihl ihr {
    simp only [btree.insert],
    by_cases c₁ : (k < tk),
    { simp only [if_pos c₁], 
      by_cases c₂ : ↥(left_heavy (insert k v tl)),
      { simp only [if_pos c₂], 
        apply rotate_right_ordered,
        rw ordered at h₁ ⊢,
        cases_matching* (_ ∧ _),
        repeat { split }; try { assumption },
        { apply ihl, assumption, },
        { apply forall_insert,
          { exact c₁, },
          { assumption },
        },
      },
      { simp only [if_neg c₂],
        rw ordered at h₁ ⊢,
        cases_matching* (_ ∧ _),
        repeat { split }; try { assumption },
        { apply ihl, assumption, },
        { apply forall_insert, 
          { exact c₁, },
          { assumption, },
        }
      },
    },
    { simp only [if_neg c₁], 
      by_cases c₂ : (k > tk),
      { simp only [if_pos c₂], 
        by_cases c₃ : ↥(right_heavy (insert k v tr)),
        { simp only [if_pos c₃], 
          apply rotate_left_ordered,
          rw ordered at h₁ ⊢,
          cases_matching* (_ ∧ _),
          repeat { split }; try { assumption },
          { apply ihr, assumption, },
          { apply forall_insert,
            { exact c₂, },
            { assumption, },
          }
        },
        { simp only [if_neg c₃], 
          rw ordered at h₁ ⊢,
          cases_matching* (_ ∧ _),
          repeat { split }; try { assumption },
          { apply ihr, assumption, },
          { apply forall_insert, 
            { exact c₂, },
            { assumption, },
          },
        },
      },
      { simp only [if_neg c₂], 
        have h : k = tk := by linarith,
        subst h,
        exact h₁,
      },
    },
  },
end

lemma insert_bound (t : btree α) (k : nat) (v : α) :
  bound k (insert k v t) = tt :=
begin
  induction t,
  case empty {
    simp [btree.insert, bound],
  },
  case node : tl tk ta tr ihl ihr {
    simp [btree.insert],
    by_cases c₁ : (k < tk),
    { simp only [if_pos c₁], 
      by_cases c₂ : ↥(left_heavy (insert k v tl)),
      { simp only [if_pos c₂], 
        rw ← rotate_right_keys,
        simp [bound],
        tauto,
      },
      { simp only [if_neg c₂], 
        simp [bound],
        tauto,
      },
    },
    { simp only [if_neg c₁], 
      by_cases c₂ : (tk < k),
      { simp only [if_pos c₂], 
        by_cases c₃ : ↥(right_heavy (insert k v tr)),
        { simp only [if_pos c₃], 
          rw ← rotate_left_keys,
          simp [bound],
          tauto,
        },
        { simp only [if_neg c₃], 
          simp [bound],
          tauto,
        },
      },
      { simp [if_neg c₂, bound], },
    },
  },
end

lemma insert_diff_bound (t : btree α) (k x : nat) (v : α) :
  bound x t = tt → bound x (insert k v t) = tt :=
begin
  intro h₁,
  induction t,
  case empty {
    simp [btree.insert, bound],
    simp [bound] at h₁,
    contradiction,
  },
  case node : tl tk ta tr ihl ihr {
    simp only [btree.insert],
    by_cases c₁ : (k < tk),
    { simp only [if_pos c₁], 
      by_cases c₂ : ↥(left_heavy (insert k v tl)),
      { simp only [if_pos c₂], 
        rw ← rotate_right_keys,
        simp [bound],
        simp [bound] at h₁,
        tauto,
      },
      { simp only [if_neg c₂], 
        simp [bound],
        simp [bound] at h₁,
        tauto,
      },
    },
    { simp only [if_neg c₁], 
      by_cases c₂ : (k > tk),
      { simp only [if_pos c₂], 
        by_cases c₃ : ↥(right_heavy (insert k v tr)),
        { simp only [if_pos c₃], 
          rw ← rotate_left_keys,
          simp [bound],
          simp [bound] at h₁,
          tauto,
        },
        { simp only [if_neg c₃],
          simp [bound],
          simp [bound] at h₁,
          tauto,
        },
      },
      { simp only [if_neg c₂], 
        simp [bound],
        simp [bound] at h₁,
        have h : k = tk := by linarith,
        subst h,
        exact h₁,
      },
    },
  },
end

lemma insert_nbound (t : btree α) (k x : nat) (v : α) :
  (bound x t = ff ∧ x ≠ k) → bound x (insert k v t) = ff :=
begin
  intro h₁,
  induction t,
  case empty {
    simp [btree.insert, bound],
    finish,
  },
  case node : tl tk ta tr ihl ihr {
    simp only [btree.insert],
    by_cases c₁ : (k < tk),
    { simp only [if_pos c₁],
      by_cases c₂ : ↥(left_heavy (insert k v tl)),
      { simp only [if_pos c₂], 
        rw ← rotate_right_keys,
        simp [bound] at *,
        tauto,
      },
      { simp only [if_neg c₂],
        simp [bound] at *,
        tauto, 
      }, 
    },
    { simp only [if_neg c₁], 
      by_cases c₂ : (tk < k),
      { simp only [if_pos c₂], 
        by_cases c₃ : ↥(right_heavy (insert k v tr)),
        { simp only [if_pos c₃],
          rw ← rotate_left_keys,
          simp [bound] at *,
          tauto, 
        },
        { simp only [if_neg c₃], 
          simp [bound] at *,
          tauto,
        },
      },
      { simp only [if_neg c₂], 
        simp [bound] at *,
        tauto,
      },
    },
  },
end

lemma insert_balanced (t : btree α) (k : nat) (v : α) :
  balanced t = tt → balanced (insert k v t) = tt :=
begin
  intro h₁,
  cases t,
  case empty {
    simp [btree.insert, balanced],
  },
  case node : tl tk ta tr {
    simp [btree.insert],
    by_cases c₁ : (k < tk),
    { simp only [if_pos c₁], 
      by_cases c₂ : ↥(left_heavy (insert k v tl)),
      { simp only [if_pos c₂], 
        apply rotate_right_balanced,
        sorry,
      },
      { simp only [if_neg c₂],
        simp [balanced] at h₁ ⊢,
        by_cases c₃ : (height tr ≤ height (insert k v tl)),
        { simp only [if_pos c₃], 
          sorry,
        },
        { simp only [if_neg c₃], 
          sorry,
        },
      },
    },
    { simp only [if_neg c₁], 
      by_cases c₂ : (tk < k),
      { simp only [if_pos c₂], 
        sorry,
      },
      { sorry },
    },
  },
end

end insertion_balanced_lemmas