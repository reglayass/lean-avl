import btree
import forall_keys
import tactic.linarith
set_option pp.generalized_field_notation false

namespace ordered_lemmas
open btree_def
open forall_keys_lemmas

lemma ordered_insert {α : Type} (t : btree α) (k : nat) (a : α) :
  ordered t → ordered (insert k a t) :=
begin
  intro h₁,
  induction t,
  case empty {
    simp only [btree_def.insert, ordered],
    finish,
  },
  case node : tl tk ta tr ihl ihr {
    simp only [btree_def.insert],
    simp only [ordered] at h₁,
    by_cases c₁ : (k < tk),
    { simp only [if_pos c₁, ordered], 
      apply and.intro,
      { apply ihl; finish,
      },
      { apply and.intro, 
        { finish, },
        { apply and.intro,
          { apply forall_insert, 
            { exact c₁, },
            { finish, }
          },
          { finish, } 
        }
      }
    },
    { simp only [if_neg c₁], 
      by_cases c₂ : (k > tk),
      { simp only [if_pos c₂, ordered], 
        apply and.intro,
        { finish, },
        { apply and.intro,
          { apply ihr; finish,
          },
          { apply and.intro, 
            { finish, },
            { apply forall_insert,
              { exact c₂, },
              { finish, } 
            }
          } 
        }
      },
      { simp only [if_neg c₂, ordered],
        apply and.intro,
        { finish, },
        { apply and.intro, 
          { finish, },
          { have h : k = tk := by linarith,
            apply and.intro, 
            { subst h, finish, },
            { subst h, finish, }
          }
        }
      }
    }
  }
end

-- inversion lemmas!

lemma bound_lookup {α : Type} (t : btree α) (k : nat) :
  bound k t → ∃ (v : α), lookup k t = some v :=
begin
  intros h₁,
  induction t,
  case empty {
    simp only [lookup],
    simp [bound] at h₁,
    contradiction,
  },
  case node : tl tk ta tr ihl ihr {
    simp only [lookup],
    by_cases c₁ : (k < tk),
    { simp only [if_pos c₁],
      apply ihl,
      simp only [bound, if_pos c₁] at h₁, 
      finish,
    },
    { simp only [if_neg c₁], 
      by_cases c₂ : (k > tk),
      { simp only [if_pos c₂],
        apply ihr,
        simp only [bound, if_pos c₂, if_neg c₁] at h₁,
        finish, 
      },
      { simp only [if_neg c₂], 
        existsi ta,
        refl,
      },
    }
  }
end

end ordered_lemmas