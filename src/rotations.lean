import basic
import tactic.linarith
import tactic.omega
set_option pp.generalized_field_notation false

universe u

namespace rotation_lemmas
open btree

variables {α : Type u}

lemma forall_keys_trans (r : btree α) (p : nat → nat → Prop) (z x : nat) (h₁ : p x z) (h₂ : ∀ a b c, p a b → p b c → p a c) :
  forall_keys p r z → forall_keys p r x :=
begin
  induction r,
  case empty { simp [forall_keys], },
  case node : rl rk ra rr ihl ihr { 
    simp [forall_keys],
    intros h₃ h₄ h₅,
    split,
    { finish, },
    { split, 
      { apply h₂, apply h₁, finish, },
      { finish, },
    },
  },
end

lemma easyL_ord (t : btree α) :
  ordered t → ordered (easyL t) :=
begin
  intro h₁,
  cases t,
  case empty { simp [easyL, ordered], },
  case node : tl tk ta tr {
    cases tr,
    case empty {
      simp [easyL],
      exact h₁,
    },
    case node : trl trk tra trr {
      simp [easyL, ordered, forall_keys] at *,
      cases_matching* (_ ∧ _),
      repeat { split }; try { assumption },
      apply forall_keys_trans _ (>) tk,
      { assumption },
      { apply trans, },
      { assumption, },
    },
  },
end

lemma easyR_ord (t : btree α) :
  ordered t → ordered (easyR t) :=
begin
  intro h₁,
  cases t,
  case empty {
    simp [easyR, ordered],
  },
  case node : tl tk ta tr {
    cases tl,
    case empty {
      simp [easyR],
      exact h₁,
    },
    case node: tll tlk tla tlr {
      simp [easyR, ordered, forall_keys] at *,
      cases_matching* (_ ∧ _),
      repeat { split }; try { assumption },
      apply forall_keys_trans _ (<) tk _,
      { assumption, },
      { apply trans, },
      { assumption, },
    },
  }
end

lemma rotL_ordered (t : btree α) :
  ordered t → ordered (rotL t) :=
begin
  intro h₁,
  cases t,
  case empty {
    simp [rotL, ordered],
  },
  case node : l k a r {
    cases r,
    case empty {
      simp [rotL],
      exact h₁,
    },
    case node: rl rk ra rr {
      simp [rotL],
      by_cases c₁ : (height rr < height rl),
      { simp only [if_pos c₁],
        cases rl,
        case empty {
          simp [easyR],
          apply easyL_ord,
          exact h₁,
        },
        case node : rll rlk rla rlr {
          simp only [easyR, easyL, ordered, forall_keys] at *,
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
        apply easyL_ord,
        exact h₁,
      },
    },
  }
end

lemma rotR_ordered (t : btree α) :
  ordered t → ordered (rotR t) :=
begin
  intro h₁,
  cases t,
  case empty {
    simp [rotR, ordered],
  },
  case node : l k a r {
    cases l,
    case empty {
      simp [rotR],
      exact h₁,
    },
    case node : ll lk la lr {
      simp [rotR],
      by_cases c₁ : (height ll < height lr),
      { simp [if_pos c₁], 
        cases lr,
        case empty {
          simp [easyL],
          apply easyR_ord,
          exact h₁,
        },
        case node: lrl lrk lra lrr {
          simp only [easyL, easyR, ordered, forall_keys] at *,
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
        apply easyR_ord,
        exact h₁,
      },
    },
  },
end

lemma easyL_keys (t : btree α) (k : nat) (x : bool) :
  bound k t = x → bound k (easyL t) = x :=
begin
  cases t,
  case empty {
    simp [easyL],
  },
  case node : tl tk ta tr {
    intro h₁,
    cases tr,
    case empty {
      simp [easyL],
      assumption,
    },
    case node : trl trk tra trr {
      simp [easyL, bound],
      simp [bound] at h₁,
      finish,
    },
  },
end

lemma easyR_keys (t : btree α) (k : nat) (x : bool) :
  bound k t = x → bound k (easyR t) = x :=
begin
  cases t,
  case empty {
    simp [easyR],
  },
  case node : tl tk ta tr {
    intros h₁,
    cases tl,
    case empty {
      simp [easyR],
      assumption,
    },
    case node : tll tlk tla tlr {
      simp [easyR, bound],
      simp [bound] at h₁,
      finish,
    },
  },
end

lemma rotR_keys (t : btree α) (k : nat) (x : bool) :
  bound k t = x → bound k (rotR t) = x :=
begin
  cases t,
  case empty {
    simp [rotR],
  },
  case node : tl tk ta tr {
    intro h₁,
    cases tl,
    case empty {
      simp [rotR],
      assumption,
    },
    case node : tll tlk tla tlr {
      simp [rotR],
      by_cases c₁ : (height tll < height tlr),
      { simp only [if_pos c₁],
        apply easyR_keys,
        cases tlr,
        case empty {
          simp [easyL],
          assumption,
        },
        case node : tlrl tlrk tlra tlrr {
          simp [easyL, bound],
          simp [bound] at h₁,
          finish,
        } 
      },
      { simp only [if_neg c₁], 
        apply easyR_keys,
        assumption,
      },
    },
  },
end

lemma rotL_keys (t : btree α) (k : nat) (x : bool) :
  bound k t = x → bound k (rotL t) = x :=
begin
  cases t,
  case empty {
    simp [rotL],
  },
  case node : tl tk ta tr {
    intro h₁,
    cases tr,
    case empty {
      simp [rotL],
      assumption,
    },
    case node : trl trk tra trr {
      simp [rotL],
      by_cases c₁ : (height trr < height trl),
      { simp only [if_pos c₁], 
        apply easyL_keys,
        cases trl,
        case empty {
          simp [easyR],
          assumption,
        },
        case node : trll trlk trla trlr {
          simp [easyR, bound],
          simp [bound] at h₁,
          finish,
        }
      },
      { simp only [if_neg c₁],
        apply easyL_keys,
        assumption, 
      },
    },
  },
end

lemma easyL_balanced (t : btree α) :
  outRight t → balanced (easyL t) :=
begin
  intro h₁,
  cases t,
  case empty {
    simp [easyL, balanced],
  },
  case node : tl tk ta tr {
    cases tr,
    case empty {
      simp [easyL, balanced],
      simp [outRight] at h₁,
      contradiction,
    },
    case node : trl trk tra trr {
      simp [easyL, balanced, height],
      simp [outRight] at h₁,
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
    }
  }
end

-- example (x y : nat) : x ≤ y → 1 + x ≤ 1 + y := by library_search
-- example (x y z : nat) : x ≤ z → y ≤ z → max x y ≤ z := by library_search
-- example (x y : nat) : x ≤ y → max y x = y := by library_search

lemma easyR_balanced (t : btree α) :
  outLeft t → 
    balanced (easyR t) :=
begin
  intro h₁,
  cases t,
  case empty {
    simp [easyR, balanced],
  },
  case node : tl tk ta tr {
    cases tl,
    case empty {
      simp [easyR, balanced],
      simp [outLeft] at h₁,
      contradiction,
    },
    case node : tll tlk tla tlr {
      simp [easyR, balanced, height],
      simp [outLeft] at h₁,
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
    }
  }
end

end rotation_lemmas