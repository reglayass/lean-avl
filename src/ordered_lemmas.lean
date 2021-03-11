import btree
import tactic.linarith
set_option pp.generalized_field_notation false

namespace ordered_lemmas
open btree_def

lemma ordered_insert {α : Type} (t : btree α) (k : nat) (a : α) :
  ordered t → ordered (insert k a t) :=
begin
  intro h₁,
  induction t,
  case empty {
    simp only [btree_def.insert, ordered],
    apply and.intro,
    { simp },
    { apply and.intro, 
      { simp },
      { apply and.intro, 
        { simp [forall_keys] }, 
        { simp [forall_keys] } 
      }
    }
  },
  case node : tl tk ta tr ihl ihr {
    simp only [btree_def.insert],
    by_cases c₁ : (k < tk),
    { simp only [if_pos c₁, ordered],
      apply and.intro,
      { apply ihl,
        simp only [ordered] at h₁,
        apply and.elim h₁,
        intros h h', exact h },
      { apply and.intro,
        { simp only [ordered] at h₁,
          apply and.elim h₁, 
          intros h h',
          apply and.elim h', 
          clear h h', intros h h',
          exact h },
        { apply and.intro, 
          { sorry },
          { simp only [ordered] at h₁,
            apply and.elim h₁,
            intros h h',
            apply and.elim h',
            clear h h', intros h h',
            apply and.elim_right h', 
          }
        },
      }
    },
    { simp only [if_neg c₁],
      by_cases c₂ : (k > tk),
      { simp only [if_pos c₂, ordered],
        apply and.intro,
        { simp only [ordered] at h₁,
          apply and.elim h₁,
          intros h h', exact h },
        { apply and.intro, 
          { simp only [ordered] at h₁,
            apply and.elim h₁,
            intros h h',
            apply ihr,
            apply and.elim h',
            clear h h', intros h h',
            exact h },
          { apply and.intro, 
            { sorry },
            { sorry }
          }
        }, 
      },
      { simp only [if_neg c₂, ordered],
        apply and.intro, 
        { simp only [ordered] at h₁,
          apply and.elim h₁, 
          intros h h', exact h,
        },
        { apply and.intro,
          { simp only [ordered] at h₁,
            apply and.elim h₁,
            intros h h',
            apply and.elim h',
            clear h h', intros h h', exact h },
          { apply and.intro,
            { sorry },
            { sorry }
          }
        }
      }
    }
  }
end

lemma ordered_lookup {α : Type} (t : btree α) (k : nat) (a : α) :
  ordered t ∧ bound k t → (lookup k t = some a) :=
begin 
  intro h₁,
  induction t, 
  case empty {
    simp only [lookup],
    sorry
  },
  case node : tl tk ta tr ihl ihr {
    simp only [lookup],
    by_cases c₁ : (k < tk),
    { simp only [if_pos c₁],
      apply ihl,
      apply and.elim h₁,
      intros h h',
      apply and.intro, 
      { simp only [ordered] at h,
        apply and.elim h, 
        clear h h', intros h h',
        exact h
      },
      { sorry },
    },
    { simp only [if_neg c₁],
      by_cases c₂ : (k > tk),
      { simp only [if_pos c₂],
        apply ihr,
        apply and.intro,
        apply and.elim h₁,
        intros h h',
        { simp only [ordered] at h, 
          apply and.elim h, 
          clear h h', intros h h',
          apply and.elim h', 
          clear h h', intros h h', 
          exact h 
        },
        { sorry } 
      },
      { simp only [if_neg c₂],
        sorry, 
      }
    }
  }
end

lemma unique_keys_nb {α : Type} (t : btree α) (k : nat) :
  ordered t ∧ bound k t = ff → treeElems t k = [] :=
begin
  intro h₁,
  induction t, 
  case empty {
    simp [treeElems],
  },
  case node : tl tk ta tr ihl ihr {
    simp only [treeElems],
    by_cases c₁ : (k = tk),
    { simp only [if_pos c₁],
      sorry 
    },
    { simp only [if_neg c₁],
      sorry
    }
  }
end

end ordered_lemmas