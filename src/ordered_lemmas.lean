import btree
set_option pp.generalized_field_notation false

namespace ordered_lemmas
open btree_def 

lemma ordered_insert {α : Type} (p : nat → btree α → Prop) (t : btree α) (k : nat) (a : α) :
  ordered p t → p k t → ordered p (insert k a t) :=
begin
  intros h₁ h₂,
  induction t,
  case empty {
    simp only [btree_def.insert, ordered],
    apply and.intro,
    { simp },
    { apply and.intro, 
      simp, apply and.intro, apply h₂, exact h₂},
  },
  case node : tl tk ta tr ihl ihr {
    simp only [btree_def.insert],
    by_cases c₁ : (k < tk),
    { simp only [if_pos c₁, ordered],
      apply and.intro, 
      { apply ihl, 
        { simp [ordered] at h₁, apply and.elim h₁,
          intros h h', exact h, }, 
        { sorry }, 
      },
      { apply and.intro, 
        { simp [ordered] at h₁, apply and.elim h₁,
          intros h h', apply and.elim h',
          intros h₁ h₂, exact h₁, },
        { apply and.intro, 
          { sorry },
          { simp [ordered] at h₁, apply and.elim h₁,
            intros h h', apply and.elim h',
            intros h₃ h₄, apply and.elim h₄, 
            intros h₅ h₆, exact h₆, }, 
        },
      },
    },
    { simp only [if_neg c₁],
      by_cases c₂ : (k > tk),
      { simp only [if_pos c₂, ordered],
        apply and.intro, 
        { simp only [ordered] at h₁,
          apply and.elim h₁,
          intros h h', exact h, },
        { simp only [ordered] at h₁,
          apply and.intro,
          { apply ihr,
            { apply and.elim h₁,
              intros h h',
              apply and.elim h',
              intros h₃ h₄, exact h₃,
            },
            { sorry },
          },
          { apply and.intro,
            { sorry },
            { sorry },
          }, 
        }, 
      },
      { sorry }, 
    },
  },
end

lemma ordered_lookup {α : Type} (p : nat → btree α → Prop) (s : btree α) (k : nat) (v : α):
  (ordered p s ∧ (bound k s)) → ((lookup k s) = some v) :=
begin
  intro h₁,
  induction s,
  case empty {
    simp only [lookup], 
    sorry,
  },
  case node : sl sk sa sr ihl ihr {
    simp only [lookup],
    by_cases h₂ : (k < sk),
    { simp only [if_pos h₂], apply ihl, 
      simp [ordered] at h₁, 
      sorry, 
    },
    { simp only [if_neg h₂],
      by_cases h₃ : (k > sk),
      { simp [if_pos h₃],
        apply ihr, sorry },
      { simp [if_neg h₃], sorry } }
  }
end

end ordered_lemmas