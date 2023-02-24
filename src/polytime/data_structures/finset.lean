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

@[complexity] lemma to_multiset : (λ x : list α, (↑x : multiset α)) ∈ₑ PTIME :=
by { rw complexity_class.mem_iff_comp_encode', complexity using λ x, x.insertion_sort lift_le, simp [list.merge_sort_eq_insertion_sort], }

instance {α : Type} [polycodable α] : polycodable (multiset α) :=
⟨complexity_class.decodable_of_quotient_mk (polycodable.poly (list α)) to_multiset⟩ 

instance {α : Type} [decidable_eq α] [polycodable α] : polycodable (finset α) :=
⟨complexity_class.decodable_of_equiv $ complexity_class.subtype_decode (polycodable.poly _) multiset_nodup⟩

@[complexity] lemma multiset_map {m : α → multiset β} {f : α → β → γ} (hm : m ∈ₑ PTIME) (hf : f ∈ₑ PTIME) :
  (λ x, (m x).map (f x)) ∈ₑ PTIME :=
by { complexity using λ x, ↑(((m x).sort lift_le).map (f x)), rw [← multiset.coe_map, multiset.sort_eq], }

@[complexity] lemma multiset_add : ((+) : multiset α → multiset α → multiset α) ∈ₑ PTIME :=
by { complexity using λ x y, ↑(x.sort lift_le ++ y.sort lift_le), simp only [← multiset.coe_add, multiset.sort_eq], }

@[complexity] lemma multiset_map_dep {β γ : α → Type} [∀ x, tencodable (β x)] [∀ x, tencodable (γ x)] {m : ∀ x, multiset (β x)}
  {f : ∀ x, β x → γ x} (hm : m ∈ₐ PTIME) (hf : f ∈ₐ PTIME) : (λ x, ((m x).map (f x) : multiset _)) ∈ₐ PTIME :=
polytime.functor_map_dep multiset hm hf (@multiset_map _ _ _ _ _ _)

lemma multiset_add_dep {β : α → Type} [∀ x, tencodable (β x)] {m₁ m₂ : ∀ x, multiset (β x)} 
  (hm₁ : m₁ ∈ₐ PTIME) (hm₂ : m₂ ∈ₐ PTIME) : (λ x, (m₁ x) + (m₂ x)) ∈ₐ PTIME :=
begin
  rw polytime.mem_dep_iff_comp_eq_encode (λ x (y : multiset (β x)), y.map encode) (λ x y, complexity_class.multiset_map_encode y) at ⊢ hm₁ hm₂,
  simp only [multiset.map_add] at *,
  complexity,
end

end polytime
