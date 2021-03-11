import btree
set_option pp.generalized_field_notation false

namespace ordered_lemmas
open btree_def

lemma ordered_insert {α : Type} (t : btree α) (k : nat) (a : α) :
  ordered t → ordered (insert k a t) :=
begin
  sorry
end

lemma ordered_lookup {α : Type} (t : btree α) (k : nat) (a : α) :
  ordered t ∧ bound k t → (lookup k t = some a) :=
begin 
  sorry
end

lemma unique_keys_nb {α : Type} (t : btree α) (k : nat) :
  ordered t ∧ bound k t = ff → treeElems t k = [] :=
begin
  sorry
end

end ordered_lemmas