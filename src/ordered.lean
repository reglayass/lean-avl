import basic
import tactic.linarith
set_option pp.generalized_field_notation false

universe u

namespace ordered
open btree

variables {α : Type u}

lemma forall_insert (k k' : nat) (t : btree α) (a : α) (p : nat → nat → Prop) (h₀ : p k' k) :
  forall_keys p t k' → forall_keys p (insert k a t) k' :=
begin
  intro h₁,
  induction t,
  case empty {
    simp only [btree.insert, forall_keys],
    simp only [forall_keys] at h₁,
    apply and.intro h₁ (and.intro h₀ h₁),
  },
  case node : tl tk ta tr ihl ihr {
    simp only [btree.insert],
    simp only [forall_keys] at h₁,
    by_cases c₁ : (k < tk),
    { simp only [if_pos c₁, forall_keys], 
      apply and.intro,
      { apply ihl; finish, },
      { finish, },
    },
    { simp only [if_neg c₁],
      by_cases c₂ : (k > tk),
      { simp only [if_pos c₂], 
        simp only [forall_keys],
        apply and.intro,
        { finish, },
        { apply and.intro, 
          { finish, },
          { apply ihr; finish, },
        },
      },
      { simp only [if_neg c₂, forall_keys],
        apply and.intro,
        { finish, },
        { finish, },
      }, 
    },
  },
end

lemma ordered_insert (t : btree α) (k : nat) (a : α) :
  ordered t → ordered (insert k a t) :=
begin
  intro h₁,
  induction t,
  case empty {
    simp only [btree.insert, ordered],
    finish,
  },
  case node : tl tk ta tr ihl ihr {
    simp only [btree.insert],
    simp only [ordered] at h₁,
    by_cases c₁ : (k < tk),
    { simp only [if_pos c₁, ordered], 
      apply and.intro,
      { apply ihl; finish, },
      { apply and.intro, 
        { finish, },
        { apply and.intro,
          { apply forall_insert, 
            { exact c₁, },
            { finish, },
          },
          { finish, },
        },
      },
    },
    { simp only [if_neg c₁], 
      by_cases c₂ : (k > tk),
      { simp only [if_pos c₂, ordered], 
        apply and.intro,
        { finish, },
        { apply and.intro,
          { apply ihr; finish, },
          { apply and.intro, 
            { finish, },
            { apply forall_insert,
              { exact c₂, },
              { finish, },
            },
          }, 
        },
      },
      { simp only [if_neg c₂, ordered],
        apply and.intro,
        { finish, },
        { apply and.intro, 
          { finish, },
          { have h : k = tk := by linarith,
            apply and.intro, 
            { subst h, finish, },
            { subst h, finish, },
          },
        },
      },
    },
  },
end

end ordered