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
    { sorry },
    { apply and.intro, 
      { sorry },
      { apply and.intro, apply h₂, apply h₂, } }
  },
  case node : tl tk ta tr ihl ihr {
    simp only [btree_def.insert],
    by_cases h₃ : (k < tk),
    { simp only [if_pos h₃, btree_def.insert, ordered],
      apply and.intro, 
      { sorry }, 
      { apply and.intro, 
        { sorry }, 
        { sorry } 
      }, 
    },
    { simp only [if_neg h₃],
      by_cases h₄ : (k > tk),
      { simp only [if_pos h₄], sorry },
      { simp only [if_neg h₄], sorry }
    }
  },
end

lemma ordered_lookup {α : Type} (p : nat → btree α → Prop) (s : btree α) (k : nat) (v : α):
  (ordered p s ∧ (bound k s)) → ((lookup k s) = v) :=
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
    { sorry },
    { simp only [if_neg h₂],
      by_cases h₃ : (k > sk),
      { sorry },
      { sorry } 
    },
  },
end

end ordered_lemmas