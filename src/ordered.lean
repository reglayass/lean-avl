import btree
import tactic.linarith
set_option pp.generalized_field_notation false

namespace ordered
open btree

def forall_keys {α : Type} (p : nat → nat → Prop) : nat → btree α → Prop
| x btree.empty := tt
| x (btree.node l k a r) :=
  forall_keys x l ∧ (p x k) ∧ forall_keys x r


lemma forall_insert {α : Type} (k k' : nat) (t : btree α) (a : α) (p : nat → nat → Prop) (h₀ : p k' k) :
  forall_keys p k' t → forall_keys p k' (insert k a t) :=
begin
  intro h₁,
  induction t,
  case empty {
    simp only [btree.insert, forall_keys],
    simp only [forall_keys] at h₁,
    apply and.intro h₁ (and.intro h₀ h₁)
  },
  case node : tl tk ta tr ihl ihr {
    simp only [btree.insert],
    simp only [forall_keys] at h₁,
    by_cases c₁ : (k < tk),
    { simp only [if_pos c₁, forall_keys], 
      apply and.intro,
      { apply ihl, 
        apply and.left h₁,
      },
      { apply and.right h₁ }
    },
    { simp only [if_neg c₁],
      by_cases c₂ : (k > tk),
      { simp only [if_pos c₂], 
        simp only [forall_keys],
        apply and.intro,
        { apply and.left h₁ },
        { apply and.intro, 
          { apply and.left (and.right h₁) },
          { apply ihr,
            apply and.right (and.right h₁),
          }
        }
      },
      { simp only [if_neg c₂, forall_keys],
        apply and.intro,
        { apply and.left h₁ },
        { apply and.intro h₀ (and.right (and.right h₁)), }
      } 
    }
  },
end

/--
  A binary tree is ordered when both left and right subtrees of the
  root node satisfy the predicate that each left subtree has keys
  less than the root, and each right subtree has keys more than the root.
-/
def ordered {α: Type} : btree α → Prop
| btree.empty := tt
| (btree.node l k a r) := ordered l ∧ ordered r ∧ (forall_keys (>) k l) ∧ (forall_keys (<) k r)

lemma ordered_insert {α : Type} (t : btree α) (k : nat) (a : α) :
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

end ordered