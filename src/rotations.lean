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

lemma easyL_ordered (rl rr l : btree α) (k rk : nat) (a ra : α) :
  ordered (btree.node l k a (btree.node rl rk ra rr)) → 
    ordered (easyL (btree.node l k a (btree.node rl rk ra rr))) :=
begin
  intro h₁,
  simp only [easyL, ordered],
  simp only [ordered] at h₁,
  split,
  { split, 
    { apply and.left h₁, },
    { split, 
      { apply and.left (and.left (and.right h₁)), },
      { apply and.elim h₁,
        intros h₂ h₃,
        apply and.elim h₃,
        intros h₄ h₅,
        apply and.elim h₅,
        intros h₆ h₇,
        rw forall_keys at h₇,
        apply and.intro h₆ (and.left h₇), 
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
        split,
        { apply forall_keys_trans _ (>) k _, 
          { apply and.left (and.right h₇), },
          { apply trans, },
          { exact h₆, },
        },
        { split, apply and.left (and.right h₇), finish, },
      },
      { finish, },
    } 
  },
end

lemma easyR_ordered (ll lr r : btree α) (k lk : nat) (a la : α) : 
  ordered (btree.node (btree.node ll lk la lr) k a r) → 
    ordered (easyR (btree.node (btree.node ll lk la lr) k a r)) :=
begin
  intro h₁,
  simp only [easyR, ordered],
  simp only [ordered] at h₁,
  apply and.intro,
  { apply and.left (and.left h₁), },
  { apply and.intro,
    { apply and.intro, 
      { apply and.left (and.right (and.left h₁)), },
      { apply and.intro, 
        { apply and.left (and.right h₁), },
        { apply and.intro,
          { apply and.elim h₁, 
            intros h₂ h₃,
            apply and.elim h₃,
            intros h₄ h₅,
            apply and.elim h₅,
            intros h₆ h₇,
            rw forall_keys at h₆,
            apply and.right (and.right h₆),
          },
          { finish, },
        },
      },
    },
    { apply and.intro, 
      { apply and.left (and.right (and.right (and.left h₁))), },
      { rw forall_keys, 
        apply and.intro,
        { apply and.right (and.right (and.right (and.left h₁))), },
        { apply and.elim h₁,
          intros h₂ h₃,
          apply and.elim h₃,
          intros h₄ h₅,
          apply and.elim h₅,
          intros h₆ h₇,
          rw forall_keys at h₆,
          apply and.intro,
          { apply and.left (and.right h₆), },
          { apply forall_keys_trans _ (<) k _, 
            { apply and.left (and.right h₆), },
            { apply has_lt.lt.trans, },
            { exact h₇, },
          }, 
        },
      },
    }, 
  },
end

lemma easyR_balanced (ll lr r : btree α) (lk k : nat) (la a : α) :
  outLeft (btree.node (btree.node ll lk la lr) k a r) → balanced (easyR (btree.node (btree.node ll lk la lr) k a r)) :=
begin
  sorry,
end

lemma easyL_keys (l rl rr : btree α) (k rk : nat) (a ra : α) :
  bound k (btree.node l k a (btree.node rl rk ra rr)) → bound k (easyL (btree.node l k a (btree.node rl rk ra rr))) :=
begin
  intro h,
  simp only [easyL, bound],
  simp only [bound] at h,
  by_cases c₁ :(k < k),
  { exfalso, linarith, },
  { simp only [if_neg c₁], 
    simp only [if_neg c₁] at h,
    by_cases c₂ : (k < rk),
    { simp [if_pos c₂], 
    },
    { by_cases c₃ : (k > rk),
      { sorry },
      { simp [if_neg c₂, if_neg c₃], },
    },
  },
end

end rotation_lemmas