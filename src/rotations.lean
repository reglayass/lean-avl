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

lemma easyL_ordered (rl rr l : btree α) (k rk : nat) (a ra : α) :
  ordered (btree.node l k a (btree.node rl rk ra rr)) → 
    ordered (easyL (btree.node l k a (btree.node rl rk ra rr))) :=
begin
  intro h₁,
  simp only [easyL, ordered],
  simp only [ordered] at h₁,
  apply and.elim h₁,
  intros h₂ h₃,
  apply and.elim h₃,
  intros h₄ h₅,
  apply and.elim h₅,
  intros h₆ h₇,
  rw forall_keys at h₇,
  split,
  { split, 
    { apply and.left h₁, },
    { apply and.intro (and.left (and.left (and.right h₁))) (and.intro h₆ (and.left h₇)) },
  },
  { apply and.intro,
    { apply and.left (and.right h₄), },
    { apply and.intro, 
      { rw forall_keys, 
        split,
        { apply forall_keys_trans _ (>) k _, 
          { apply and.left (and.right h₇), },
          { apply trans, },
          { exact h₆, },
        },
        { split, apply and.left (and.right h₇), finish, },
      },
      { apply and.right (and.right (and.right h₄)), },
    } 
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
        sorry,
      },
    }
  }
end

example (x y : nat) : x ≤ y → 1 + x ≤ 1 + y := by library_search
example (x y z : nat) : x ≤ z → y ≤ z → max x y ≤ z := by library_search

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
        sorry,
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

lemma easyR_ordered (ll lr r : btree α) (k lk : nat) (a la : α) : 
  ordered (btree.node (btree.node ll lk la lr) k a r) → 
    ordered (easyR (btree.node (btree.node ll lk la lr) k a r)) :=
begin
  intro h₁,
  simp only [easyR, ordered],
  simp only [ordered] at h₁,
  apply and.elim h₁,
  intros h₂ h₃,
  apply and.elim h₃,
  intros h₄ h₅,
  apply and.elim h₅,
  intros h₆ h₇,
  rw forall_keys at h₆,
  split,
  { apply and.left (and.left h₁), },
  { split,
    { split, 
      { apply and.left (and.right (and.left h₁)), },
      { apply and.intro (and.left (and.right h₁)) (and.intro (and.right (and.right h₆)) h₇), },
    },
    { split, 
      { apply and.left (and.right (and.right (and.left h₁))), },
      { rw forall_keys, 
        split,
        { apply and.right (and.right (and.right (and.left h₁))), },
        { split,
          { apply and.left (and.right h₆), },
          { apply forall_keys_trans _ (<) k _, 
            { apply and.left (and.right h₆), },
            { apply has_lt.lt.trans, },
            { exact h₇, },
          }, 
        },
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

lemma rotL_ordered (rl rr l : btree α) (k rk : nat) (a ra : α) :
  ordered (btree.node l k a (btree.node rl rk ra rr)) → 
    ordered (rotL (btree.node l k a (btree.node rl rk ra rr))) :=
begin
  intro h₁,
  simp only [rotL],
  by_cases c₁ : (height rr < height rl),
  { simp only [if_pos c₁],
    cases rl,
    case empty {
      simp only [easyR],
      apply easyL_ordered,
      exact h₁,
    },
    case node : rll rlk rla rlr {
      simp only [easyR, easyL, ordered],
      simp only [ordered] at h₁,
      apply and.elim h₁,
      intros h₂ h₃,
      apply and.elim h₃,
      intros h₄ h₅,
      apply and.elim h₅,
      intros h₆ h₇,
      apply and.elim h₄,
      intros hh₁ hh₂,
      apply and.elim hh₂,
      intros hh₃ hh₄,
      apply and.elim hh₄,
      intros hh₅ hh₆,
      split,
      { split, 
        { exact h₂, },
        { split, 
          { apply and.left (and.left h₄), },
          { split, 
            { apply and.left h₅, },
            { rw forall_keys at h₅, 
              rw forall_keys at h₅,
              apply and.left (and.left (and.right h₅)),
            },
          },
        },
      },
      { split, 
        { split, 
          { apply and.left (and.right (and.left h₄)), },
          { split, 
            { apply and.left (and.right h₄), },
            { split, 
              { rw forall_keys at hh₅,
                apply and.right (and.right hh₅),
              },
              { apply and.right (and.right (and.right h₄)), },
            },
          },
        },
        { split, 
          { rw forall_keys,
            rw forall_keys at h₇,
            rw forall_keys at h₇, 
            split,
            { apply forall_keys_trans l (>) k _,
              { apply and.left (and.right (and.left h₇)), },
              { apply trans, },
              { exact h₆, },
            },
            { split,  
              { apply and.left (and.right (and.left h₇)), },
              { apply and.left (and.right (and.right (and.left h₄))), }, 
            },
          },
          { rw forall_keys,
            rw forall_keys at hh₅, 
            split,
            { apply and.right (and.right (and.right (and.left h₄))), },
            { split, 
              { apply and.left (and.right hh₅), },
              { apply forall_keys_trans rr (<) rk _, 
                { apply and.left (and.right hh₅), },
                { apply has_lt.lt.trans, },
                { exact hh₆, },
              },
            },
          },
        },
      },
    },
  },
  { simp only [if_neg c₁], 
    apply easyL_ordered,
    exact h₁,
  },
end

lemma rotR_ordered (ll lr r : btree α) (k lk : nat) (a la : α) : 
  ordered (btree.node (btree.node ll lk la lr) k a r) → 
    ordered (rotR (btree.node (btree.node ll lk la lr) k a r)) :=
begin
  intro h₁,
  simp only [rotR],
  by_cases c₁ : (height ll < height lr),
  { simp only [if_pos c₁], 
    cases lr,
    case empty {
      apply easyR_ordered,
      exact h₁,
    },
    case node : lrl lrk lra lrr {
      simp only [easyL, easyR, ordered],
      simp only [ordered] at h₁,
      apply and.elim h₁,
      intros h₂ h₃,
      apply and.elim h₂,
      intros h₄ h₅,
      apply and.elim h₅,
      intros h₆ h₇,
      apply and.elim h₃,
      intros hh₁ hh₂,
      apply and.elim hh₂,
      intros hh₃ hh₄,
      rw forall_keys at hh₃,
      rw forall_keys at hh₃,
      split,
      { split, 
        { exact h₄, },
        { split, 
          { apply and.left h₆, },
          { split, 
            { apply and.left h₇, },
            { rw forall_keys at h₇, 
              apply and.left (and.right h₇),
            },
          },
        },
      },
      { split, 
        { split, 
          { apply and.left (and.right h₆), },
          { split, 
            { exact hh₁, },
            { apply and.intro
              (and.right (and.right (and.right (and.right hh₃))))
              (and.right (and.right h₃)),
            },
          },
        },
        { split, 
          { rw forall_keys, 
            rw forall_keys at h₇,
            split,
            { apply forall_keys_trans ll (>) lk _, 
              { apply and.left (and.right (and.right h₇)), },
              { apply trans, },
              { apply and.left h₇, },
            },
            { apply and.intro 
              (and.left (and.right (and.right h₇))) 
              (and.left (and.right (and.right h₆))), 
            },
          },
          { rw forall_keys,
            split,
            { apply and.right (and.right (and.right h₆)), },
            { split, 
              { apply and.left (and.right (and.right (and.right hh₃))), },
              { apply forall_keys_trans r (<) k _,
                { apply and.left (and.right (and.right (and.right hh₃))), },
                { apply has_lt.lt.trans, },
                { exact hh₄, },
              },
            },
          },
        },
      },
    },
  },
  { simp only [if_neg c₁],
    apply easyR_ordered,
    exact h₁,
  },
end

end rotation_lemmas