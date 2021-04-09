import btree
import tactic.linarith
set_option pp.generalized_field_notation false

namespace forall_keys_lemmas
open btree_def

lemma forall_insert {α : Type} (tk k : nat) (tl : btree α) (a : α) (p : nat → nat → Prop) (h : p k tk) :
  forall_keys p tk tl → forall_keys p tk (insert k a tl) :=
begin
  sorry 
end

end forall_keys_lemmas