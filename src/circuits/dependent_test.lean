import circuits.circuit_encoding

open_locale complexity_class
open tencodable

variables {α : Type} {β : α → Type} {β₁ : α → Type} {β₂ : α → Type}
  [tencodable α] [∀ x, tencodable (β x)] [∀ x, tencodable (β₁ x)] [∀ x, tencodable (β₂ x)]

def complexity_class.mem_types (β : α → Type) [∀ x, tencodable (β x)]
  [∀ x, fintype (β x)] (C : complexity_class) : Prop :=
∃ (f : tree unit → finset (tree unit)), f ∈ₑ C ∧
  ∀ x : α, f (encode x) = (finset.univ : finset (β x)).map ⟨encode, encode_injective⟩ 

def complexity_class.mem_dep (f : ∀ x, β x) (C : complexity_class) : Prop :=
∃ (f' : tree unit → tree unit), f' ∈ₑ C ∧
  ∀ x : α, f' (encode x) = encode (f x)

localized "infix ` ∈ₜ `:50 := complexity_class.mem_types" in complexity_class
localized "infix ` ∈ₐ `:50 := complexity_class.mem_dep" in complexity_class

theorem polytime_fin_n : fin ∈ₜ PTIME := sorry 

-- theorem polytime_list_map_dep {ls : ∀ x, list (β₁ x)} {f : ∀ x, β₁ x → β₂ x} 
--   (h : ls ∈ₐ PTIME)






