import definitions
import ordered
import tactic.linarith
import tactic.omega
set_option pp.generalized_field_notation false

universe u

namespace rotation_lemmas
open btree
open ordered

variables {α : Type u}

lemma forall_simple_left (k' k : nat) (l r : btree α) (a : α) (p : nat → nat → Prop) (h : p k' k) :
  forall_keys p k' (btree.node l k a r) → forall_keys p k' (simple_left (btree.node l k a r)) :=
begin
  intro h₁,
  cases r,
  case empty {
    simp [simple_left],
    assumption,
  },
  case node : rl rk ra rr {
    simp [simple_left],
    rw forall_keys at *,
    cases_matching* (_ ∧ _),
    rw forall_keys at h₁_right_right,
    cases_matching* (_ ∧ _),
    repeat { split }; assumption,
  }
end

lemma forall_simple_right (k' k : nat) (l r : btree α) (a : α) (p : nat → nat → Prop) (h : p k' k) :
  forall_keys p k' (btree.node l k a r) → forall_keys p k' (simple_right (btree.node l k a r)) :=
begin
  intro h₁,
  cases l,
  case empty {
    simp [simple_right],
    assumption,
  },
  case node : ll lk la lr {
    simp [simple_right],
    rw forall_keys at *,
    cases_matching* (_ ∧ _),
    rw forall_keys at h₁_left,
    cases_matching* (_ ∧ _),
    repeat { split }; assumption,
  }
end

lemma forall_rotate_left (k' k : nat) (l r : btree α) (a : α) (p : nat → nat → Prop) (h : p k' k) :
  forall_keys p k' (btree.node l k a r) → forall_keys p k' (rotate_left (btree.node l k a r)) :=
begin
  intro h₁,
  cases r,
  case empty {
    simp [rotate_left],
    assumption,
  },
  case node : rl rk ra rr {
    simp [rotate_left],
    by_cases c₁ : (height rr < height rl),
    { simp only [if_pos c₁], 
      apply forall_simple_left,
      { assumption },
      { rw forall_keys at *, 
        cases_matching* (_ ∧ _),
        rw forall_keys at h₁_right_right,
        cases_matching* (_ ∧ _),
        repeat { split }; try { assumption },
        { apply forall_simple_right,
          { assumption },
          { rw forall_keys,
            repeat { split }; assumption,
          },
        },
      },
    },
    { simp only [if_neg c₁], 
      apply forall_simple_left,
      { assumption },
      { rw forall_keys at *,
        cases_matching* (_ ∧ _),
        rw forall_keys at h₁_right_right,
        cases_matching* (_ ∧ _),
        repeat { split }; assumption,
      },
    },
  },
end

lemma forall_rotate_right (k' k : nat) (l r : btree α) (a : α) (p : nat → nat → Prop) (h : p k' k) :
  forall_keys p k' (btree.node l k a r) → forall_keys p k' (rotate_right (btree.node l k a r)) :=
begin
  intro h₁,
  cases l,
  case empty {
    simp [rotate_right],
    assumption,
  },
  case node : ll lk la lr {
    simp [rotate_right],
    by_cases c₁ : (height ll < height lr),
    { simp only [if_pos c₁],
      apply forall_simple_right, 
      { assumption, },
      { rw forall_keys at *, 
        cases_matching* (_ ∧ _),
        rw forall_keys at h₁_left,
        cases_matching* (_ ∧ _),
        repeat { split }; try { assumption },
        { apply forall_simple_left, 
          { assumption, },
          { rw forall_keys,  
            repeat { split }; assumption,
          }
        },
      },
    },
    { simp only [if_neg c₁], 
      apply forall_simple_right; assumption,
    }
  }
end

/- Simple left rotations preserve order -/
lemma simple_left_ord (t : btree α) :
  ordered t → ordered (simple_left t) :=
begin
  intro h₁,
  cases t,
  case empty { simp [simple_left, ordered], },
  case node : tl tk ta tr {
    cases tr,
    case empty {
      simp [simple_left],
      exact h₁,
    },
    case node : trl trk tra trr {
      simp [simple_left, ordered, forall_keys] at *,
      cases_matching* (_ ∧ _),
      repeat { split }; try { assumption },
      apply forall_keys_trans _ (>) tk,
      { assumption },
      { apply trans, },
      { assumption, },
    },
  },
end

/- Simple right rotations preserve order -/
lemma simple_right_ord (t : btree α) :
  ordered t → ordered (simple_right t) :=
begin
  intro h₁,
  cases t,
  case empty {
    simp [simple_right, ordered],
  },
  case node : tl tk ta tr {
    cases tl,
    case empty {
      simp [simple_right],
      exact h₁,
    },
    case node: tll tlk tla tlr {
      simp [simple_right, ordered, forall_keys] at *,
      cases_matching* (_ ∧ _),
      repeat { split }; try { assumption },
      apply forall_keys_trans _ (<) tk _,
      { assumption, },
      { apply trans, },
      { assumption, },
    },
  }
end

/- Left rotations preserve order -/
lemma rotate_left_ordered (t : btree α) :
  ordered t → ordered (rotate_left t) :=
begin
  intro h₁,
  cases t,
  case empty {
    simp [rotate_left, ordered],
  },
  case node : l k a r {
    cases r,
    case empty {
      simp [rotate_left],
      exact h₁,
    },
    case node: rl rk ra rr {
      simp [rotate_left],
      by_cases c₁ : (height rr < height rl),
      { simp only [if_pos c₁],
        cases rl,
        case empty {
          simp [simple_right],
          apply simple_left_ord,
          exact h₁,
        },
        case node : rll rlk rla rlr {
          simp only [simple_right, simple_left, ordered, forall_keys] at *,
          cases_matching* (_ ∧ _),
          repeat {split} ; try { assumption },
          { apply forall_keys_trans l (>) k, 
            { assumption, },
            { apply trans, },
            { assumption, },
          },
          { apply forall_keys_trans rr (<) rk _, 
            { assumption, },
            { apply trans, },
            { assumption, },
          }, 
        },
      },
      { simp [if_neg c₁], 
        apply simple_left_ord,
        exact h₁,
      },
    },
  },
end

/- Right rotations preserve order -/
lemma rotate_right_ordered (t : btree α) :
  ordered t → ordered (rotate_right t) :=
begin
  intro h₁,
  cases t,
  case empty {
    simp [rotate_right, ordered],
  },
  case node : l k a r {
    cases l,
    case empty {
      simp [rotate_right],
      exact h₁,
    },
    case node : ll lk la lr {
      simp [rotate_right],
      by_cases c₁ : (height ll < height lr),
      { simp [if_pos c₁], 
        cases lr,
        case empty {
          simp [simple_left],
          apply simple_right_ord,
          exact h₁,
        },
        case node: lrl lrk lra lrr {
          simp only [simple_left, simple_right, ordered, forall_keys] at *,
          cases_matching* (_ ∧ _),
          repeat { split };  try { assumption },
          { apply forall_keys_trans ll (>) lk _,
            { assumption, },
            { apply trans, },
            { assumption, },
          },
          { apply forall_keys_trans r (<) k _, 
            { assumption },
            { apply trans, },
            { assumption },
          },
        },
      },
      { simp [if_neg c₁], 
        apply simple_right_ord,
        exact h₁,
      },
    },
  },
end

/- Simple left rotations preserve pre-existing keys -/
lemma simple_left_keys (t : btree α) (k : nat) (x : bool) :
  bound k t = x → bound k (simple_left t) = x :=
begin
  cases t,
  case empty {
    simp [simple_left],
  },
  case node : tl tk ta tr {
    intro h₁,
    cases tr,
    case empty {
      simp [simple_left],
      assumption,
    },
    case node : trl trk tra trr {
      simp [simple_left, bound],
      simp [bound] at h₁,
      finish,
    },
  },
end

/- Simple right rotations preserve pre-existing keys -/
lemma simple_right_keys (t : btree α) (k : nat) (x : bool) :
  bound k t = x → bound k (simple_right t) = x :=
begin
  cases t,
  case empty {
    simp [simple_right],
  },
  case node : tl tk ta tr {
    intros h₁,
    cases tl,
    case empty {
      simp [simple_right],
      assumption,
    },
    case node : tll tlk tla tlr {
      simp [simple_right, bound],
      simp [bound] at h₁,
      finish,
    },
  },
end

/- Right rotations preserve pre-existing keys -/
lemma rotate_right_keys (t : btree α) (k : nat) (x : bool) :
  bound k t = x → bound k (rotate_right t) = x :=
begin
  cases t,
  case empty {
    simp [rotate_right],
  },
  case node : tl tk ta tr {
    intro h₁,
    cases tl,
    case empty {
      simp [rotate_right],
      assumption,
    },
    case node : tll tlk tla tlr {
      simp [rotate_right],
      by_cases c₁ : (height tll < height tlr),
      { simp only [if_pos c₁],
        apply simple_right_keys,
        cases tlr,
        case empty {
          simp [simple_left],
          assumption,
        },
        case node : tlrl tlrk tlra tlrr {
          simp [simple_left, bound],
          simp [bound] at h₁,
          finish,
        } 
      },
      { simp only [if_neg c₁], 
        apply simple_right_keys,
        assumption,
      },
    },
  },
end

/- Left rotations preserve pre-existing keys -/
lemma rotate_left_keys (t : btree α) (k : nat) (x : bool) :
  bound k t = x → bound k (rotate_left t) = x :=
begin
  cases t,
  case empty {
    simp [rotate_left],
  },
  case node : tl tk ta tr {
    intro h₁,
    cases tr,
    case empty {
      simp [rotate_left],
      assumption,
    },
    case node : trl trk tra trr {
      simp [rotate_left],
      by_cases c₁ : (height trr < height trl),
      { simp only [if_pos c₁], 
        apply simple_left_keys,
        cases trl,
        case empty {
          simp [simple_right],
          assumption,
        },
        case node : trll trlk trla trlr {
          simp [simple_right, bound],
          simp [bound] at h₁,
          finish,
        }
      },
      { simp only [if_neg c₁],
        apply simple_left_keys,
        assumption, 
      },
    },
  },
end

/- If a tree is right-heavy, a simple left rotations restores balance -/
lemma simple_left_balanced (t : btree α) :
  right_heavy t → balanced (simple_left t) :=
begin
  intro h₁,
  cases t,
  case empty {
    simp [simple_left, balanced],
  },
  case node : tl tk ta tr {
    cases tr,
    case empty {
      simp [simple_left, balanced],
      simp [right_heavy] at h₁,
      contradiction,
    },
    case node : trl trk tra trr {
      simp [simple_left, balanced, height],
      simp [right_heavy] at h₁,
      cases_matching* (_ ∧ _),
      by_cases c₁ : (height trr ≤ 1 + max (height tl) (height trl)),
      { simp [if_pos c₁], 
        rw ← h₁_right_right_right at *,
        suffices h : 1 + max (height tl) (height trl) ≤ 1 + (height tl + 1),
        { omega, },
        apply (add_le_add_iff_left 1).mpr,
        apply max_le, 
        { simp, },
        { assumption, },
      },
      { simp [if_neg c₁], 
        rw ← h₁_right_right_right at *,
        rw max_eq_left h₁_right_right_left,
        linarith,
      },
    },
  },
end

/-  If a tree is left-heavy, a simple right rotation preserves balance -/
lemma simple_right_balanced (t : btree α) :
  left_heavy t → 
    balanced (simple_right t) :=
begin
  intro h₁,
  cases t,
  case empty {
    simp [simple_right, balanced],
  },
  case node : tl tk ta tr {
    cases tl,
    case empty {
      simp [simple_right, balanced],
      simp [left_heavy] at h₁,
      contradiction,
    },
    case node : tll tlk tla tlr {
      simp [simple_right, balanced, height],
      simp [left_heavy] at h₁,
      cases_matching* (_ ∧ _), 
      by_cases c₁ : (1 + max (height tlr) (height tr) ≤ height tll),
      { simp [if_pos c₁], 
        rw max_eq_left h₁_right_right_left,
        linarith,
      },
      { simp [if_neg c₁],
        rw ← h₁_right_right_right at *,
        suffices h : 1 + max (height tlr) (height tr) ≤ 1 + (height tr + 1),
        { omega, },
        apply (add_le_add_iff_left 1).mpr,
        apply max_le,
        { assumption, },
        { simp, },
      },
    },
  },
end

/- If a tree is left-heavy, a right rotation restores balance -/
lemma rotate_right_balanced (t : btree α) :
  left_heavy t → balanced (rotate_right t) :=
begin
  intro h₁,
  cases t,
  case empty {
    simp [rotate_right, balanced],
  },
  case node : l k a r {
    cases l,
    case empty {
      simp [rotate_right, balanced],
      simp [left_heavy] at h₁,
      contradiction,
    },
    case node : tl tk ta tr {
      simp [rotate_right],
      by_cases c₁ : (height tl < height tr),
      { simp [if_pos c₁], 
        cases tr,
        case empty {
          simp [simple_left],
          apply simple_right_balanced,
          exact h₁,
        },
        case node : trl trk tra trr {
          simp [simple_left, simple_right, balanced, height],
          simp [left_heavy, height] at h₁,
          cases_matching* (_ ∧ _),
          by_cases c₂ : (height trr ≤ height tl ∧ height r ≤ height tl ∨ height trr ≤ height trl ∧ height r ≤ height trl),
          { sorry },
          { sorry },
        },
      },
      { simp [if_neg c₁],
        apply simple_right_balanced,
        exact h₁,
      }
    }
  }
end

/- If a tree is right-heavy, a left rotation restores balance -/
lemma rotate_left_balanced (t : btree α) :
  right_heavy t → balanced (rotate_left t) :=
begin
  intro h₁,
  cases t,
  case empty {
    simp [rotate_left, balanced],
  },
  case node : l k a r {
    cases r,
    case empty {
      simp [rotate_left, balanced],
      simp [right_heavy] at h₁,
      contradiction,
    },
    case node : tl tk ta tr {
      simp [rotate_left],
      by_cases c₁ : (height tr < height tl),
      { simp [if_pos c₁],
        cases tl,
        case empty {
          simp [simple_right],
          apply simple_left_balanced,
          exact h₁,
        },
        case node : tll tlk tla tlr {
          simp [simple_right, simple_left, balanced, height],
          simp [right_heavy, height] at h₁,
          sorry,
        }
      },
      { simp [if_neg c₁],
        apply simple_left_balanced,
        exact h₁,
      },
    }
  }
end

end rotation_lemmas