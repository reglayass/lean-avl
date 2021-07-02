import definitions
import forall_keys
import tactic.linarith
set_option pp.generalized_field_notation false

universe u

namespace ordered_lemmas
open btree
open forall_keys_lemmas

variables {α : Type u}

/- Insertion into an ordered tree preserves order -/
lemma ordered_insert (t : btree α) (k : nat) (a : α) :
  ordered t → ordered (insert k a t) :=
begin
  intro h₁,
  induction t,
  case empty {
    simp [btree.insert, ordered],
    repeat { split }; simp [forall_keys],
    repeat { intros k' h₂, contradiction, },
  },
  case node : tl tk ta tr ihl ihr {
    simp [btree.insert],
    by_cases c₁ : (k < tk),
    { simp only [if_pos c₁, ordered], 
      rw ordered at h₁,
      cases_matching* (_ ∧ _),
      repeat { split },
      { apply ihl, assumption, },
      { assumption, },
      { apply forall_insert; assumption, },
      { assumption, },
    },
    { simp only [if_neg c₁], 
      by_cases c₂ : (tk < k),
      { simp only [if_pos c₂, ordered], 
        rw ordered at h₁,
        cases_matching* (_ ∧ _),
        repeat { split },
        { assumption, },
        { apply ihr, assumption, },
        { assumption, },
        { apply forall_insert; assumption, },
      },
      { simp only [if_neg c₂], 
        have h : tk = k := by linarith,
        subst h,
        exact h₁,
      },
    },
  },
end

end ordered_lemmas