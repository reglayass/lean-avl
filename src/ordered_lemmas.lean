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
      simp,
      apply and.intro,
      { simp [forall_keys] },
      { simp [forall_keys] }
    }
  },
  case node : tl tk ta tr ihl ihr {
    simp only [btree_def.insert],
    by_cases c₁ : (k < tk),
    { simp only [if_pos c₁, ordered],
      apply and.intro,
      { apply ihl,
        simp [ordered] at h₁,
        apply and.elim_left h₁ 
      },
      { apply and.intro,
        { simp [ordered] at h₁,
          apply and.elim h₁,
          intros h₂ h₃,
          apply and.elim_left h₃
        },
        { sorry }
      }
    },
    { simp only [if_neg c₁], 
      by_cases c₂ : (k > tk),
      { simp [if_pos c₂, ordered],
        apply and.intro,
        { simp [ordered] at h₁, 
          apply and.elim_left h₁
        },
        { apply and.intro,
          { apply ihr, 
            simp [ordered] at h₁,
            apply and.elim h₁,
            intros h₂ h₃,
            apply and.elim_left h₃
          },
          { sorry }
        } 
      },
      { simp only [if_neg c₂, ordered], 
        apply and.intro,
        { simp [ordered] at h₁, 
          apply and.elim_left h₁,
        },
        { apply and.intro,
          { simp [ordered] at h₁, 
            apply and.elim h₁,
            intros h₂ h₃,
            apply and.elim_left h₃,
          },
          { sorry } 
        }
      }
    }
  }
end

lemma ordered_lookup {α : Type} (t : btree α) (k : nat) (v : α) :
  ordered t ∧ bound k t → (lookup k t = some v) :=
begin
  intro h₁,
  induction t,
  case empty {
    simp only [lookup],
    apply and.elim h₁,
    intros h₂ h₃,
    simp [bound] at h₃,
    exact h₃,
  },
  case node : tl tk ta tr ihl ihr {
    simp only [lookup],
    by_cases c₁ : (k < tk),
    { simp [if_pos c₁], 
      apply ihl,
      apply and.intro,
      { apply and.elim h₁,
        intros h₂ h₃,
        simp [ordered] at h₂,
        apply and.elim_left h₂,
      },
      { apply and.elim h₁, 
        intros h₂ h₃,
        simp only [bound, if_pos c₁] at h₃,
        exact h₃,
      } 
    },
    { simp [if_neg c₁], 
      by_cases c₂ : (tk < k),
      { simp only [if_pos c₂], 
        apply ihr,
        apply and.elim h₁,
        intros h₂ h₃,
        simp [ordered] at h₂,
        apply and.elim h₂,
        intros h₄ h₅,
        simp [bound, if_neg c₁, if_pos c₂] at h₃,
        exact and.intro (and.elim_left h₅) h₃,
      },
      { simp only [if_neg c₂], sorry }
    }
  }
end

end ordered_lemmas