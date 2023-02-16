import polytime.data_structures.list

namespace polytime

open_locale complexity_class
open tencodable function polysize

variables {α β γ δ ε η : Type} [tencodable α] [tencodable β] [tencodable γ]
 [tencodable δ] [tencodable ε] [tencodable η]

@[complexity] lemma polytime_lift_le : (@lift_le α _) ∈ₚ PTIME :=
by { dunfold lift_le, complexity, }

@[complexity] lemma multiset_nodup : (@multiset.nodup α) ∈ₚ PTIME :=
by { complexity using λ s, (s.sort lift_le).nodup, simpa using (@multiset.coe_nodup _ (s.sort lift_le)).symm, }

@[complexity] lemma to_multiset : (show list α → multiset α, from @quotient.mk _ (list.is_setoid α)) ∈ₑ PTIME :=
by { rw complexity_class.mem_iff_comp_encode', complexity using λ x, x.insertion_sort lift_le, simp [list.merge_sort_eq_insertion_sort], }

instance {α : Type} [polycodable α] : polycodable (multiset α) :=
⟨complexity_class.decodable_of_quotient_mk (polycodable.poly (list α)) to_multiset⟩ 

instance {α : Type} [decidable_eq α] [polycodable α] : polycodable (finset α) :=
⟨complexity_class.decodable_of_equiv $ complexity_class.subtype_decode (polycodable.poly _) multiset_nodup⟩

end polytime
