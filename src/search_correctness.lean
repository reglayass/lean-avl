import btree
set_option pp.generalized_field_notation false

namespace search_correct
open btree_def 

lemma bst_insert_inv {α : Type} (t' : nat → α → Prop) (t : btree α) (k : nat) (v: α) :
  t' k v → bst_inv t' (insert k v t) :=
begin
  intro h₁,
  induction t,
  case empty {
    sorry
  },
  sorry
end

-- Theorem insert_BST : ∀ (V : Type) (k : key) (v : V) (t : tree V),
--     BST t → BST (insert k v t).
-- Proof.
--   (* FILL IN HERE *) Admitted.

end search_correct