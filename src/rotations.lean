import definitions forall_keys tactic.linarith tactic.omega
set_option pp.generalized_field_notation false

universe u

namespace rotation_lemmas
open btree forall_keys_lemmas

variables {α : Type u}

lemma forall_simple_left (x k : nat) (l r : btree α) (a : α) (p : nat → nat → Prop) :
  forall_keys p x (btree.node l k a r) → forall_keys p x (simple_left (btree.node l k a r)) :=
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
    intros k' h₂,
    simp [bound] at h₂,
    cases_matching* (_ ∨ _),
    repeat {
      apply h₁,
      simp [bound],
      tauto,
    },
  },
end

lemma forall_simple_right (x k : nat) (l r : btree α) (a : α) (p : nat → nat → Prop) :
  forall_keys p x (btree.node l k a r) → forall_keys p x (simple_right (btree.node l k a r)) :=
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
    intros k' h₂,
    simp [bound] at h₂,
    cases_matching* (_ ∨ _),
    repeat {
      apply h₁,
      simp [bound],
      tauto,
    },
  },
end

lemma forall_rotate_left (x k : nat) (l r : btree α) (a : α) (p : nat → nat → Prop) :
  forall_keys p x (btree.node l k a r) → forall_keys p x (rotate_left (btree.node l k a r)) :=
begin
  intro h₁,
  cases r,
  case empty {
    simp [rotate_left],
    exact h₁,
  },
  case node : rl rk ra rr {
    simp [rotate_left],
    by_cases c₁ : (height rr < height rl),
    { simp only [if_pos c₁],
      apply forall_simple_left, 
      rw ← forall_keys_intro,
      repeat { split },
      { unfold forall_keys at h₁ ⊢, 
        intros k' h₂,
        apply h₁,
        simp [bound],
        apply or.inr (or.inl h₂),
      },
      { unfold forall_keys at h₁, 
        apply h₁,
        simp [bound],
      },
      { apply forall_simple_right, 
        unfold forall_keys at h₁ ⊢,
        intros k' h₂,
        apply h₁,
        simp [bound] at h₂ ⊢,
        tauto,
      },
    },
    { simp only [if_neg c₁], 
      apply forall_simple_left,
      exact h₁,
    },
  },
end

lemma forall_rotate_right (x k : nat) (l r : btree α) (a : α) (p : nat → nat → Prop) :
  forall_keys p x (btree.node l k a r) → forall_keys p x (rotate_right (btree.node l k a r)) :=
begin
  intro h₁,
  cases l,
  case empty {
    simp [rotate_right],
    exact h₁,
  },
  case node : ll lk la lr {
    simp [rotate_right],
    by_cases c₁ : (height ll < height lr),
    { simp only [if_pos c₁], 
      apply forall_simple_right,
      rw ← forall_keys_intro,
      repeat { split },
      { apply forall_simple_left, 
        unfold forall_keys at h₁ ⊢,
        intros k' h₂,
        apply h₁,
        simp [bound] at h₂ ⊢,
        tauto,
      },
      { unfold forall_keys at h₁, 
        apply h₁,
        simp [bound],
      },
      { unfold forall_keys at h₁ ⊢, 
        intros k' h₂,
        apply h₁,
        simp [bound],
        apply or.inr (or.inr h₂),
      },
    },
    { simp only [if_neg c₁], 
      apply forall_simple_right,
      exact h₁,
    },
  },
end

/- Simple left rotations preserve order -/
lemma simple_left_ordered (t : btree α) :
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
      simp [simple_left],
      simp [ordered] at h₁ ⊢,
      cases_matching* (_ ∧ _),
      repeat { split }; try { assumption },
      { unfold forall_keys at h₁_right_right_right ⊢, 
        intros k' h₂,
        apply h₁_right_right_right,
        simp [bound],
        apply or.inr (or.inl h₂),
      },
      { rw ← forall_keys_intro,
        repeat { split },
        { apply forall_keys_trans _ (>) tk, 
          { unfold forall_keys at h₁_right_right_right, 
            apply h₁_right_right_right,
            simp [bound],
          },
          { apply trans, },
          { assumption, },
        },
        { unfold forall_keys at h₁_right_right_right, 
          apply h₁_right_right_right,
          simp [bound],
        },
        { assumption, },
      },
    },
  },
end

/- Simple right rotations preserve order -/
lemma simple_right_ordered (t : btree α) :
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
    case node : tll tlk tla tlr {
      simp [simple_right],
      simp [ordered] at h₁ ⊢,
      cases_matching* (_ ∧ _),
      repeat { split }; try { assumption },
      { unfold forall_keys at h₁_right_right_left ⊢, 
        intros k' h₂,
        apply h₁_right_right_left,
        simp [bound],
        apply or.inr (or.inr h₂),
      },
      { rw ← forall_keys_intro, 
        repeat { split },
        { assumption, },
        { unfold forall_keys at h₁_right_right_left, 
          apply h₁_right_right_left,
          simp [bound],
        },
        { apply forall_keys_trans _ (<) tk, 
          { unfold forall_keys at h₁_right_right_left, 
            apply h₁_right_right_left,
            simp [bound],
          },
          { apply trans, },
          { assumption, },
        },
      },
    },
  },
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
    case node : rl rk ra rr {
      simp only [rotate_left],
      by_cases c₁ : (height rr < height rl),
      { simp only [if_pos c₁], 
        apply simple_left_ordered,
        cases rl,
        case empty {
          simp [simple_right],
          exact h₁,
        },
        case node : rll rlk rla rlr {
          simp only [simple_right],
          simp only [ordered] at h₁ ⊢,
          cases_matching* (_ ∧ _),
          repeat { split }; try { assumption },
          { unfold forall_keys at h₁_right_left_right_right_left ⊢, 
            intros k' h₂,
            apply h₁_right_left_right_right_left,
            simp [bound],
            apply or.inr (or.inr h₂),
          },
          { rw ← forall_keys_intro,
            repeat { split },
            { assumption, },
            { unfold forall_keys at h₁_right_left_right_right_left, 
              apply h₁_right_left_right_right_left,
              simp [bound],
            },
            { apply forall_keys_trans _ (<) rk,
              { unfold forall_keys at h₁_right_left_right_right_left, 
                apply h₁_right_left_right_right_left,
                simp [bound],
              },
              { apply trans, },
              { assumption, },
            },
          },
          { unfold forall_keys at h₁_right_right_right ⊢,
            intros k' h₂,
            apply h₁_right_right_right,
            simp [bound] at h₂ ⊢,
            tauto,
          },
        }
      },
      { simp only [if_neg c₁], 
        apply simple_left_ordered,
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
      { simp only [if_pos c₁], 
        apply simple_right_ordered,
        cases lr,
        case empty {
          simp only [simple_left],
          exact h₁,
        },
        case node : lrl lrk lra lrr {
          simp only [simple_left],
          simp only [ordered] at h₁ ⊢,
          cases_matching* (_ ∧ _),
          repeat { split }; try { assumption },
          { unfold forall_keys at h₁_left_right_right_right ⊢, 
            intros k' h₂,
            apply h₁_left_right_right_right,
            simp [bound],
            apply or.inr (or.inl h₂),
          },
          { rw ← forall_keys_intro, 
            repeat { split },
            { apply forall_keys_trans _ (>) lk,
              { unfold forall_keys at h₁_left_right_right_right, 
                apply h₁_left_right_right_right,
                simp [bound],
              },
              { apply trans, },
              { assumption, },
            },
            { unfold forall_keys at h₁_left_right_right_right, 
              apply h₁_left_right_right_right,
              simp [bound],
            },
            { assumption, },
          },
          { unfold forall_keys at h₁_right_right_left ⊢, 
            intros k' h₂,
            apply h₁_right_right_left,
            simp [bound] at h₂ ⊢,
            tauto,
          },
        },
      },
      { simp only [if_neg c₁], 
        apply simple_right_ordered,
        exact h₁,
      },
    },
  },
end

/- Simple left rotations preserve pre-existing keys -/
lemma simple_left_keys (t : btree α) (k : nat) (x : bool) :
  bound k t = x ↔ bound k (simple_left t) = x :=
begin
  cases t,
  case empty {
    split; simp [simple_left],
  },
  case node : tl tk ta tr {
    cases tr,
    case empty {
      split; simp [simple_left],
    },
    case node : trl trk tra trr {
      simp [simple_left, bound],
      split; { intro h₁, finish, },
    },
  },
end

/- Simple right rotations preserve pre-existing keys -/
lemma simple_right_keys (t : btree α) (k : nat) (x : bool) :
  bound k t = x ↔ bound k (simple_right t) = x :=
begin
  cases t,
  case empty {
    split; simp [simple_right],
  },
  case node : tl tk ta tr {
    cases tl,
    case empty {
      split; simp [simple_right],
    },
    case node : tll tlk tla tlr {
      simp [simple_right, bound],
      split; { intro h₁, finish, },
    },
  },
end

/- Right rotations preserve pre-existing keys -/
lemma rotate_right_keys (t : btree α) (k : nat) (x : bool) :
  bound k t = x ↔ bound k (rotate_right t) = x :=
begin
  cases t,
  case empty {
    split; simp [rotate_right],
  },
  case node : tl tk ta tr {
    cases tl,
    case empty {
      split; simp [rotate_right],
    },
    case node : tll tlk tla tlr {
      simp [rotate_right],
      by_cases c₁ : (height tll < height tlr),
      { simp only [if_pos c₁], 
        split,
        { intro h₁,
          rw ← simple_right_keys,
          cases tlr,
          case empty { simp [simple_left], assumption, },
          case node : tlrl tlrk tlra tlrr {
            simp [simple_left],
            simp [bound] at h₁ ⊢,
            finish,
          },
        },
        { intro h₁, 
          rw ← simple_right_keys at h₁,
          cases tlr,
          case empty { simp [simple_left] at h₁, assumption, },
          case node : tlrl tlrk tlra tlrr {
            simp [simple_left] at h₁,
            simp [bound] at h₁ ⊢,
            finish,
          },
        },
      },
      { simp only [if_neg c₁],
        split,
        { intro h₁,
          rw ← simple_right_keys, 
          exact h₁,
        },
        { intro h₁, 
          rw ← simple_right_keys at h₁,
          exact h₁,
        },
      },
    },
  },
end

/- Left rotations preserve pre-existing keys -/
lemma rotate_left_keys (t : btree α) (k : nat) (x : bool) :
  bound k t = x ↔ bound k (rotate_left t) = x :=
begin
  cases t,
  case empty {
    split; simp [rotate_left],
  },
  case node : tl tk ta tr {
    cases tr,
    case empty {
      split; simp [rotate_left],
    },
    case node : trl trk tra trr {
      simp [rotate_left],
      by_cases c₁ : (height trr < height trl),
      { simp only [if_pos c₁], 
        split,
        { intro h₁, 
          rw ← simple_left_keys,
          cases trl,
          case empty { simp [simple_right], exact h₁, },
          case node : trll trlk trla trlr {
            simp [simple_right],
            simp [bound] at h₁ ⊢,
            finish,
          },
        },
        { intro h₁, 
          rw ← simple_left_keys at h₁,
          cases trl,
          case empty { simp [simple_right] at h₁, exact h₁, },
          case node : trll trlk trla trlr {
            simp [simple_right, bound] at h₁,
            simp [bound],
            finish,
          }
        },
      },
      { simp only [if_neg c₁], 
        split,
        { intro h₁, 
          rw ← simple_left_keys,
          exact h₁,
        },
        { intro h₁, 
          rw ← simple_left_keys at h₁,
          exact h₁,
        },
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
        apply simple_right_balanced,
        simp [left_heavy] at h₁,
        cases tr,
        case empty {
          simp [simple_left, left_heavy],
          assumption,
        },
        case node : trl trk tra trr {
          simp [simple_left, left_heavy],
          cases_matching* (_ ∧ _),
          linarith,
        }
      },
      { simp [if_neg c₁],   
        apply simple_right_balanced,
        assumption,
      },
    },
  },
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
        apply simple_left_balanced,
        simp [right_heavy] at h₁,
        cases tl,
        case empty {
          simp [simple_right, right_heavy],
          assumption,
        },
        case node : tll tlk tla tlr {
          simp [simple_right, right_heavy],
          cases_matching* (_ ∧ _),
          linarith,
        }
      },
      { simp [if_neg c₁],
        apply simple_left_balanced,
        exact h₁,
      },
    },
  },
end

end rotation_lemmas