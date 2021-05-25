import basic
import rotations
import tactic.linarith
set_option pp.generalized_field_notation false

universe u

namespace deletion_lemmas
open btree
open rotation_lemmas

variables {α : Type u}

lemma shrink_empty (t : btree α) :
  shrink (@empty_tree α) = none := by refl

lemma delRoot_empty (t : btree α) :
  delRoot (@empty_tree α) = btree.empty := by refl

lemma delRoot_ordered (t : btree α) :
  ordered t → ordered (delRoot t) :=
begin
  intro h₁,
  induction t,
  case empty {
    simp [delRoot, ordered],
  },
  case node : tl tk ta tr {
    sorry,
  }
end

/- deletion preserves order -/
-- lemma delete_ordered (t : btree α) (k : nat) :
--   ordered t → ordered (delete k t) :=
-- begin
--   intro h₁,
--   induction t,
--   case empty {
--     simp [delete, ordered],
--   },
--   case node : tl tk ta tr ihl ihr {
--     simp [delete],
--     simp [ordered] at h₁,
--     by_cases c₁ : (k = tk),
--     { simp [if_pos c₁], 
--       sorry,
--     },
--     { simp [if_neg c₁],
--       by_cases c₂ : (k < tk),
--       { simp [if_pos c₂], 
--         by_cases c₃ : (height (delete k tl) + 1 < height tr),
--         { simp only [if_pos c₃],
--           sorry,
--         },
--         { simp only [if_neg c₃, ordered],
--           split,
--           { apply ihl,
--             apply and.left h₁,
--           },
--           { split,
--             { apply and.left (and.right h₁), },
--             { split,
--               { sorry },
--               { apply and.right (and.right (and.right h₁)), },
--             },
--           },
--         },
--       },
--       { simp [if_neg c₂],
--         by_cases c₃ : (height (delete k tr) + 1 < height tl),
--         { simp [if_pos c₃], 
--           sorry,
--         },
--         { simp [if_neg c₃, ordered], 
--           split,
--           { apply and.left h₁, },
--           { split,
--             { apply ihr,
--               apply and.left (and.right h₁), 
--             },
--             { split,
--               { apply and.left (and.right (and.right h₁)), },
--               { sorry, }, 
--               -- forall_keys has_lt.lt (delete k tr) tk → forall_keys has_lt.lt tr tk
--             },
--           },
--         },
--       },
--     },
--   },
-- end

/- deletion preserves balance -/

/- deletion conserves keys -/
-- lemma delete_key_nb (t : btree α) (k : nat) :
--   bound k (delete k t) = ff :=
-- begin
--   induction t,
--   case empty {
--     simp [delete, bound],
--   },
--   case node : tl tk ta tr ihl ihr {
--     simp [delete],
--     by_cases c₁ : (k = tk),
--     { sorry, },
--     { simp [if_neg c₁],
--       by_cases c₂ : (k < tk),
--       { simp [if_pos c₂],
--         by_cases c₃ : (height (delete k tl) + 1 < height tr),
--         { simp [if_pos c₃], 
--           sorry,
--         },
--         { simp [if_neg c₃, bound],
--           split,
--           { exact c₁, },
--           { split,
--             { exact ihl, },
--             { sorry },
--           },
--         },
--       },
--       { simp [if_neg c₂],
--         by_cases c₃ : (height (delete k tr) + 1 < height tl),
--         { simp [if_pos c₃], 
--           sorry,
--         },
--         { simp [if_neg c₃, bound],
--           split,
--           { exact c₁, },
--           { split,
--             { sorry },
--             { exact ihr, }, 
--           },
--         },
--       },
--     },
--   }
-- end

end deletion_lemmas