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
      sorry,
    },
    { sorry },
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
          sorry,
        },
        { simp only [if_neg c₃],
          sorry,
        },
      },
      { simp only [if_neg c₂], 
        by_cases c₃ : (height tl > height (delete k tr) + 1),
        { sorry, },
        { simp only [if_neg c₃],
          sorry,
        },
      },
    },
  }
end

end deletion_lemmas
