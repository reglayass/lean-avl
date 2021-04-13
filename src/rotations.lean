import btree
import balanced
import tactic.linarith
set_option pp.generalized_field_notation false

namespace rotation_lemmas
open btree_def
open balanced

lemma easyR_order {α : Type} (xL xR zR : btree α) (x z : nat) (a d : α) :
  ordered (btree.node (btree.node xL x a xR) z d zR) → 
    ordered (easyR (btree.node (btree.node xL x a xR) z d zR)) :=
begin
  sorry
end

lemma easyR_balance {α : Type} (xL xR zR : btree α) (x z : nat) (a d : α) :
  outLeft (btree.node (btree.node xL x a xR) z d zR) → 
    balanced (easyR (btree.node (btree.node xL x a xR) z d zR)) :=
begin
  sorry
end

end rotation_lemmas