import definitions
import tactic.linarith
set_option pp.generalized_field_notation false

universe u

namespace ordered
open btree

variables {α : Type u}

/- Transivitity property for keys in a binary search tree -/
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

/- Order of keys previously existing does not change on new key insertion -/
lemma forall_insert (k k' : nat) (t : btree α) (a : α) (p : nat → nat → Prop) (h : p k' k) :
  forall_keys p k' t → forall_keys p k' (insert k a t) :=
begin
  intro h₁,
  induction t,
  case empty {
    simp [btree.insert, forall_keys] at *,
    assumption,
  },
  case node : tl tk ta tr ihl ihr {
    simp only [btree.insert, forall_keys] at *,
    cases_matching* (_ ∧ _),
    by_cases c₁ : (k < tk),
    { simp only [if_pos c₁, forall_keys],
      repeat { split }; try { assumption },
      { apply ihl, assumption },
    },
    { simp only [if_neg c₁], 
      by_cases c₂ : (k > tk),
      { simp only [if_pos c₂, forall_keys], 
        repeat { split }; try { assumption },
        { apply ihr, assumption, },
      },
      { simp only [if_neg c₂, forall_keys], 
        repeat { split }; try { assumption },
      },
    },
  }
end 

/- Insertion into an ordered tree preserves order -/
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
    simp only [btree.insert, ordered] at *,
    cases_matching* (_ ∧ _),
    by_cases c₁ : (k < tk),
    { simp only [if_pos c₁, ordered], 
      repeat { split }; try { assumption },
      { apply ihl, assumption, },
      { apply forall_insert; assumption, },
    },
    { simp only [if_neg c₁], 
      by_cases c₂ : (k > tk),
      { simp only [if_pos c₂, ordered], 
        repeat { split }; try { assumption },
        { apply ihr, assumption, },
        { apply forall_insert; assumption, },
      },
      { simp only [if_neg c₂, ordered], 
        have h : k = tk := by linarith,
        repeat { split }; try { assumption },
        { subst h, assumption, },
        { subst h, assumption, },
      },
    },
  }
end

end ordered