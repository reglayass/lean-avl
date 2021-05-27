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

-- lemma delRoot_empty_l (r : btree α) (k : nat) (a : α) :
--   delRoot (btree.node btree.empty k a r) = r :=
-- begin
--   simp [delRoot, shrink, delRoot_core],
-- end

lemma delRoot_ordered (t : btree α) :
  ordered t → ordered (delRoot t) :=
begin
  intro h₁,
  induction t,
  case empty {
    simp [delRoot, ordered],
  },
  case node: tl tk ta tr ihl ihr {
    cases' delRoot_delRoot_view (node tl tk ta tr),
    case nonempty_empty {
      sorry
    },
    case nonempty_nonempty₁ {
      sorry,
    },
    case nonempty_nonempty₂ {
      sorry
    }
  }
end

/- deletion preserves order -/
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
    simp [ordered] at h₁,
    by_cases c₁ : (k = tk),
    { simp [if_pos c₁],
      apply delRoot_ordered,
      rw ordered,
      assumption,
    },
    { simp [if_neg c₁],
      by_cases c₂ : (k < tk),
      { simp [if_pos c₂],
        by_cases c₃ : (height (delete k tl) + 1 < height tr),
        { simp only [if_pos c₃],
          sorry,
        },
        { simp only [if_neg c₃, ordered],
          split,
          { apply ihl,
            apply and.left h₁,
          },
          { split,
            { apply and.left (and.right h₁), },
            { split,
              { sorry },
              { apply and.right (and.right (and.right h₁)), },
            },
          },
        },
      },
      { simp [if_neg c₂],
        by_cases c₃ : (height (delete k tr) + 1 < height tl),
        { simp [if_pos c₃],
          sorry,
        },
        { simp [if_neg c₃, ordered],
          split,
          { apply and.left h₁, },
          { split,
            { apply ihr,
              apply and.left (and.right h₁),
            },
            { split,
              { apply and.left (and.right (and.right h₁)), },
              { sorry, },
            },
          },
        },
      },
    },
  },
end

end deletion_lemmas
