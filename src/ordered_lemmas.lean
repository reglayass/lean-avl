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
        simp [forall_keys],
        simp [forall_keys]
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
        apply and.elim_left h₁,
      },
      { apply and.intro,
        { simp only [ordered] at h₁,
          apply and.elim h₁,
          intros h₂ h₃,
          apply and.elim_left h₃
        },
        { apply and.intro,
          { sorry },
          { simp only [ordered] at h₁,
            apply and.elim h₁,
            intros h₂ h₃,
            apply and.elim h₃,
            intros h₄ h₅,
            apply and.elim_right h₅
          } 
        }
      } 
    },
    { simp only [if_neg c₁], 
      by_cases c₂ : (k > tk),
      { simp only [if_pos c₂, ordered],
        apply and.intro,
        { simp only [ordered] at h₁, 
          apply and.elim_left h₁
        },
        { apply and.intro, 
          { apply ihr, 
            simp only [ordered] at h₁,
            apply and.elim h₁,
            intros h₂ h₃,
            apply and.elim_left h₃
          },
          { apply and.intro,
            { simp only [ordered] at h₁,
              apply and.elim h₁,
              intros h₂ h₃,
              apply and.elim h₃,
              intros h₄ h₅,
              apply and.elim_left h₅
            },
            { sorry } 
          }
        }
      },
      { simp only [if_neg c₂, ordered],
        apply and.intro,
        { simp only [ordered] at h₁,
          apply and.elim_left h₁ 
        },
        { apply and.intro, 
          { apply and.elim h₁,
            intros h₂ h₃,
            apply and.elim_left h₃ 
          },
          { apply and.intro,
            { sorry },
            { sorry } 
          }
        } 
      }
    }
  }
end

lemma forall_insert_lt {α: Type} (k k' : nat) (a : α) (l r: btree α) (h₁ : ordered (btree.node l k' a r)) :
  (forall_keys (<) k' (insert k a l)) ∧ (forall_keys (>) k' r) :=
begin
  apply and.intro,
  { simp only [ordered] at h₁, 
    sorry, 
  },
  { simp only [ordered] at h₁, 
    apply and.elim h₁,
    intros h h',
    apply and.elim h',
    clear h h', intros h h',
    apply and.elim_right h'
  },
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
      apply and.intro,
      apply and.elim h₁,
      { intros h₂ h₃,
        simp only [ordered] at h₂,
        apply and.elim_left h₂ 
      },
      { apply and.elim h₁, 
        intros h₂ h₃,
        simp only [bound] at h₃,
        by_cases c₂ : (k > tk),
        { simp only [if_pos c₂] at h₃, 
          simp only [if_pos c₁] at h₃,
          exact h₃
        },
        { simp only [if_neg c₂] at h₃,
          simp only [if_pos c₁] at h₃,
          exact h₃
        }
      }
    },
    { simp only [if_neg c₁],
      by_cases c₂ : (k > tk),
      { simp only [if_pos c₂], 
        apply ihr,
        apply and.intro,
        { apply and.elim h₁, 
          intros h₂ h₃,
          simp only [ordered] at h₂,
          apply and.elim h₂,
          intros h₃ h₄,
          apply and.elim_left h₄
        },
        { apply and.elim h₁,
          intros h₂ h₃,
          simp only [bound] at h₃,
          simp only [if_pos c₂] at h₃,
          simp only [if_neg c₁] at h₃,
          exact h₃ 
        }
      },
      { simp only [if_neg c₂], 
        simp only [coe, lift_t, has_lift_t.lift, coe_t, has_coe_t.coe],
        sorry 
      }
    }
  }
end

end ordered_lemmas