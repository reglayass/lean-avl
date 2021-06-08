import definitions
import rotations
import tactic.linarith
import tactic.induction
set_option pp.generalized_field_notation false

universe u

namespace shrink_lemmas 
open btree
open rotation_lemmas

variables {α : Type u}

lemma shrink_shrink_view (t : btree α) : 
  shrink_view t (shrink t) :=
begin
 cases t,
 case empty {
  exact shrink_view.empty,
 },
 case node : l k a r {
  dsimp [shrink],
  cases h : shrink r,
  case none {
    dsimp only [shrink._match_1],
    apply shrink_view.nonempty_empty; assumption,
  },
  case some {
    rcases val with ⟨x, a', sh⟩,
    dsimp only [shrink._match_1],
    by_cases h' : (height l > height sh + 1),
    { simp only [if_pos h'], 
      apply shrink_view.nonempty_nonempty₁, try { assumption },
      assumption, simp,
    },
    { simp only [if_neg h'],
      apply shrink_view.nonempty_nonempty₂, try { assumption },
      linarith,
    },
  },
 },
end

/- If a tree is ordered, the shrunken tree is also ordered and the inorder predecessor is larger than all the keys in the shrunken tree-/
lemma shrink_ordered (l r sh : btree α) (k x : nat) (v a : α) :
  ordered (btree.node l k v r) ∧ shrink (btree.node l k v r) = some (x, a, sh) → (ordered sh ∧ forall_keys (>) x sh) :=
begin
  intro h₁,
  induction r generalizing x a sh l k v,
  case empty {
    simp [ordered, shrink] at h₁,
    cases_matching* (_ ∧ _),
    rw ← h₁_right_right_right,
    split,
    { assumption, },
    { subst h₁_right_left, assumption, },
  },
  case node : rl rk ra rr ihl ihr {
    cases_matching* (_ ∧ _),
    cases' shrink_shrink_view (node l k v (node rl rk ra rr)),
    case nonempty_empty { cases' h₁_right, 
      simp [ordered] at h₁_left,
      finish,
    },
    case nonempty_nonempty₁ { rw h_2 at h₁_right, 
      cases' h₁_right,
      clear h_2,
      split,
      { apply rotate_right_ordered, 
        rw ordered at *,
        { specialize ihr x_1 a_1 sh_1 rl rk ra, 
          have h : ordered (node rl rk ra rr),
          { rw ordered at *,
            rw forall_keys at *, 
            cases_matching* (_ ∧ _),
            repeat { split }; try { assumption },
          },
          specialize ihr ⟨h, h_1⟩,
          cases_matching* (_ ∧ _),
          repeat { split }; try { assumption },
          { sorry, }
        }
      },
      { sorry },
    },
    case nonempty_nonempty₂ { sorry },
  },
end

end shrink_lemmas