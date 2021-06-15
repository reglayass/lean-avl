import definitions
import rotations
import shrink
import tactic.linarith
import tactic.induction
set_option pp.generalized_field_notation false

universe u

namespace del_node_lemmas 
open btree
open rotation_lemmas
open shrink_lemmas

variables {α : Type u}

lemma del_node_del_node_view (t : btree α) :
  del_node_view t (del_node t) :=
begin
  cases t,
  case empty {
    exact del_node_view.empty,
  },
  case node : l k a r {
    dsimp [del_node],
    cases h : shrink l,
    case none {
      dsimp [del_node._match_1],
      apply del_node_view.nonempty_empty; assumption,
    },
    case some {
      rcases val with ⟨x, a', sh⟩,
      dsimp only [del_node._match_1],
      by_cases h' : height r > height sh + 1,
      { simp only [if_pos h'],
        apply del_node_view.nonempty_nonempty₁; assumption,
      },
      { simp only [if_neg h'],
        apply del_node_view.nonempty_nonempty₂; try { assumption, },
        linarith,
      },
    },
  },
end

lemma forall_del_node (t : btree α) (k : nat) (p : nat → nat → Prop) :
  forall_keys p k t → forall_keys p k (del_node t) :=
begin
  intro h₁,
  cases t,
  case empty {
    simp [del_node, forall_keys],
  },
  case node : tl tk ta tr {
    rw forall_keys at *,
    cases_matching* (_ ∧ _),
    cases' del_node_del_node_view (node tl tk ta tr),
    case nonempty_empty { assumption, },
    case nonempty_nonempty₁ {
      apply forall_rotate_left,
      { rw forall_keys, 
        repeat { split },
        { apply forall_keys_shrink_aux_1 h₁_left h, },
        { apply forall_keys_shrink_aux_2 h₁_left h, },
        { assumption, },
      },
    },
    case nonempty_nonempty₂ {
      rw forall_keys,
      repeat { split },
      { apply forall_keys_shrink_aux_1 h₁_left h, },
      { apply forall_keys_shrink_aux_2 h₁_left h, },
      { assumption, },
    },
  },
end

lemma del_node_ordered (t : btree α) :
  ordered t → ordered (del_node t) :=
begin
  intro h₁,
  cases t,
  case empty {
    simp [del_node, ordered],
  },
  case node : tl tk ta tr {
    simp [ordered] at h₁,
    cases_matching* (_ ∧ _),
    cases' del_node_del_node_view (node tl tk ta tr),
    case nonempty_empty { assumption, },
    case nonempty_nonempty₁ { 
      apply rotate_left_ordered, 
      rw ordered,
      repeat { split },
      { have h : ordered l ∧ shrink l = some (x, a, sh) := and.intro h₁_left h,
        apply shrink_ordered_aux_1 h, exact x, 
      },
      { assumption, },
      { have h : ordered l ∧ shrink l = some (x, a, sh) := and.intro h₁_left h, 
        apply shrink_ordered_aux_2 h, exact x,
      },
      { sorry, },
    },
    case nonempty_nonempty₂ { 
      rw ordered, 
      repeat { split },
      { have h : ordered l ∧ shrink l = some (x, a, sh) := and.intro h₁_left h, 
        apply shrink_ordered_aux_1 h, exact x,
      },
      { assumption, },
      { have h : ordered l ∧ shrink l = some (x, a, sh) := and.intro h₁_left h, 
        apply shrink_ordered_aux_2 h, exact x,
      },
      { sorry },
    },
  },
end

end del_node_lemmas