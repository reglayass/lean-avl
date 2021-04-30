import basic
import tactic.linarith
set_option pp.generalized_field_notation false

universe u

namespace rotation_lemmas
open btree

variables {α : Type u}

lemma forall_keys_trans (r : btree α) (p : nat → nat → Prop) (z x : nat) (h₁ : p x z) (h₂ : ∀ a b c, p a b → p b c → p a c) :
  forall_keys p z r → forall_keys p x r :=
begin
  induction r,
  case empty { simp [forall_keys], },
  case node : rl rk ra rr ihl ihr { 
    simp [forall_keys],
    intros h₃ h₄ h₅,
    split,
    { finish, },
    { split, 
      { apply h₂, apply h₁, finish, },
      { finish, },
    },
  },
end

lemma easyL_ordered (rl rr l : btree α) (x z : nat) (a d : α) :
  ordered (btree.node l z d (btree.node rl x a rr)) → 
    ordered (easyL (btree.node l z d (btree.node rl x a rr))) :=
begin
  intro h₁,
  simp only [easyL, ordered],
  simp only [ordered] at h₁,
  apply and.intro,
  { apply and.intro, 
    { finish, },
    { apply and.intro, 
      { finish, },
      { apply and.intro,
        { finish, },
        { apply and.elim h₁, 
          intros h₂ h₃,
          apply and.elim h₃,
          intros h₄ h₅,
          apply and.elim h₅,
          intros h₆ h₇,
          rw forall_keys at h₇,
          finish,
        }, 
      },
    },
  },
  { apply and.intro, 
    { finish, },
    { apply and.intro,
      { rw forall_keys, 
        apply and.elim h₁,
        intros h₂ h₃,
        apply and.elim h₃,
        intros h₄ h₅,
        apply and.elim h₅,
        intros h₆ h₇,
        rw forall_keys at h₇,
        apply and.intro,
        { apply forall_keys_trans _ (>) z _, 
          { finish, },
          { apply trans, },
          { finish, },
        },
        { apply and.intro,
          { finish, },
          { finish, }, 
        },
      },
      { finish, }, 
    },
  },
end

lemma easyR_ordered (ll lr r : btree α) (x z : nat) (a d : α) : 
  ordered (btree.node (btree.node ll x a lr) z d r) → 
    ordered (easyR (btree.node (btree.node ll x a lr) z d r)) :=
begin
  intro h₁,
  simp only [easyR, ordered],
  simp only [ordered] at h₁,
  apply and.intro,
  { finish, },
  { apply and.intro,
    { apply and.intro, 
      { finish, },
      { apply and.intro, 
        { finish, },
        { apply and.intro,
          { apply and.elim h₁, 
            intros h₂ h₃,
            apply and.elim h₃,
            intros h₄ h₅,
            apply and.elim h₅,
            intros h₆ h₇,
            rw forall_keys at h₆,
            finish,
          },
          { finish, },
        },
      },
    },
    { apply and.intro, 
      { finish, },
      { rw forall_keys, 
        apply and.intro,
        { finish, },
        { apply and.elim h₁,
          intros h₂ h₃,
          apply and.elim h₃,
          intros h₄ h₅,
          apply and.elim h₅,
          intros h₆ h₇,
          rw forall_keys at h₆,
          apply and.intro,
          { finish, },
          { apply forall_keys_trans _ (<) z _, 
            { finish, },
            { apply has_lt.lt.trans, },
            { finish, },
          }, 
        },
      },
    }, 
  },
end

lemma easyR_keys (ll lr r : btree α) (k x z : nat) (a d : α) :
  bound k (btree.node (btree.node ll x a lr) z d r) →
    bound k (easyR (btree.node (btree.node ll x a lr) z d r)) :=
begin
  intro h₁,
  simp only [bound] at h₁,
  by_cases c₁ : (k < z),
  { simp only [if_pos c₁] at h₁, 
    by_cases c₂ : (k < x), 
    { simp only [if_pos c₂] at h₁, 
      simp only [easyR, bound, if_pos c₁, if_pos c₂],
      finish,
    },
    { simp only [if_neg c₂] at h₁, 
      by_cases c₃ : (k > x),
      { simp only [if_pos c₃] at h₁, 
        simp only [easyR, bound, if_neg c₂, if_pos c₃, if_pos c₁],
        finish,
      },
      { simp only [if_neg c₃] at h₁,  
        simp only [easyR, bound, if_neg c₂, if_neg c₃],
        finish,
      },
    },
  },
  { simp only [if_neg c₁] at h₁, 
    by_cases c₂ : (k > z),
    { simp only [if_pos c₂] at h₁, 
      simp only [easyR, bound, if_neg c₁, if_pos c₂],
      sorry 
    },
    { simp only [if_neg c₂] at h₁, 
      simp only [easyR, bound, if_neg c₁, if_neg c₂],
      sorry
    },
  },
end

end rotation_lemmas