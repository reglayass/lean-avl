import basic
import rotations
import tactic.linarith
import tactic.induction
set_option pp.generalized_field_notation false

universe u

namespace deletion_lemmas
open btree
open rotation_lemmas

variables {α : Type u}

lemma delRoot_delRoot_view (t : btree α) :
  delRoot_view t (delRoot t) :=
begin
  cases t,
  case empty {
    exact delRoot_view.empty,
  },
  case node : l k a r {
    dsimp [delRoot],
    cases h : shrink l,
    case none {
      dsimp [delRoot._match_1],
      apply delRoot_view.nonempty_empty; assumption,
    },
    case some {
      rcases val with ⟨x, a', sh⟩,
      dsimp only [delRoot._match_1],
      by_cases h' : height r > height sh + 1,
      { simp only [if_pos h'],
        apply delRoot_view.nonempty_nonempty₁; assumption,
      },
      { simp only [if_neg h'],
        apply delRoot_view.nonempty_nonempty₂; try { assumption, },
        linarith,
      },
    },
  },
end

lemma shrink_shrink_view (t : btree α) : 
  shrink_view t (shrink t) :=
begin
 cases t,
 case empty {
  exact shrink_view.empty,
 },
 case node : l k a r {
  dsimp [shrink],
  cases h : shrink r,
  case none {
    dsimp only [shrink._match_1],
    apply shrink_view.nonempty_empty; assumption,
  },
  case some {
    rcases val with ⟨x, a', sh⟩,
    dsimp only [shrink._match_1],
    by_cases h' : (height l > height sh + 1),
    { simp only [if_pos h'], 
      apply shrink_view.nonempty_nonempty₁, try { assumption },
      assumption, simp,
    },
    { simp only [if_neg h'],
      apply shrink_view.nonempty_nonempty₂, try { assumption },
      linarith,
    },
  },
 },
end

lemma shrink_ordered (l r sh : btree α) (k x : nat) (v a : α) :
  ordered (btree.node l k v r) ∧ shrink (btree.node l k v r) = some (x, a, sh) → (ordered sh ∧ forall_keys (>) x sh) :=
begin
  intro h₁,
  induction r generalizing x a sh l k v,
  case empty {
    simp [ordered, shrink] at h₁,
    cases_matching* (_ ∧ _),
    rw ← h₁_right_right_right,
    split,
    { assumption, },
    { subst h₁_right_left, assumption, },
  },
  case node : rl rk ra rr ihl ihr {
    cases_matching* (_ ∧ _),
    cases' shrink_shrink_view (node l k v (node rl rk ra rr)),
    case nonempty_empty { cases' h₁_right, 
      simp [ordered] at h₁_left,
      finish,
    },
    case nonempty_nonempty₁ { rw h_2 at h₁_right, 
      cases' h₁_right,
      clear h_2,
      split,
      { apply rotR_ordered, 
        rw ordered at *,
        { specialize ihr x_1 a_1 sh_1 rl rk ra, 
          have h : ordered (node rl rk ra rr),
          { rw ordered at *,
            rw forall_keys at *, 
            cases_matching* (_ ∧ _),
            repeat { split }; try { assumption },
          },
          specialize ihr ⟨h, h_1⟩,
          cases_matching* (_ ∧ _),
          repeat { split }; try { assumption },
          { sorry, }
        }
      },
      { sorry },
    },
    case nonempty_nonempty₂ { sorry },
  },
end

lemma delRoot_ordered (t : btree α) :
  ordered t → ordered (delRoot t) :=
begin
  intro h₁,
  cases t,
  case empty {
    simp [delRoot, ordered],
  },
  case node : tl tk ta tr {
    cases' delRoot_delRoot_view (node tl tk ta tr),
    { simp only [ordered] at h₁, 
      apply and.left (and.right h₁),
    },
    { apply rotL_ordered,
      rw ordered,
      sorry,
    },
    { sorry, },
  }
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
      apply delRoot_ordered,
      exact h₁,
    },
    { simp only [if_neg c₁],
      by_cases c₂ : (k < tk),
      { simp only [if_pos c₂], 
        by_cases c₃ : (height (delete k tl) + 1 < height tr),
        { simp only [if_pos c₃],
          apply rotL_ordered,
          rw ordered at *,
          cases_matching* (_ ∧ _),
          repeat { split }; try { assumption },
          { apply ihl; assumption },
          { sorry, },
        },
        { simp only [if_neg c₃],
          rw ordered at *,
          cases_matching* (_ ∧ _),
          repeat { split }; try { assumption },
          { apply ihl; assumption, },
          { sorry },
        },
      },
      { simp only [if_neg c₂], 
        by_cases c₃ : (height tl > height (delete k tr) + 1),
        { simp only [if_pos c₃], 
          apply rotR_ordered,
          rw ordered at *,
          cases_matching* (_ ∧ _),
          repeat { split }; try { assumption },
          { apply ihr; assumption, },
          { sorry },
        },
        { simp only [if_neg c₃],
          rw ordered at *,
          cases_matching* (_ ∧ _),
          repeat { split }; try { assumption },
          { apply ihr; assumption, },
          { sorry },
        },
      },
    },
  }
end

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
          apply rotL_keys,
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
          apply rotR_keys,
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
