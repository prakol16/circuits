import circuits.circuit_encoding

namespace function
/- Note that Lean fails to infer something like
(infer_instance : ∀ x : α, has_uncurry (list (β x) → list (β x) → list (β x)) _ _)
unless all the underscores are made explicit for some reason.
(infer_instance : ∀ x : α, has_uncurry (list (β x) → list (β x) → list (β x)) (list (β x) × list (β x)) (list $ β x))

This is why we make the following instances
-/
universes u v
variables {α : Type} {β β₁ β₂ γ δ : α → Type}

class has_uncurry_dep {α : Type} (β : α → Type) (β₁ β₂ : out_param (α → Type)) :=
(uncurry : ∀ {x}, (β x) → ((β₁ x) → (β₂ x)))

notation (name := uncurry_dep) `↾`:max x:max := has_uncurry_dep.uncurry _ x

instance has_uncurry_dep_base : has_uncurry_dep (λ x, (β₁ x → β₂ x)) β₁ β₂ := ⟨λ x y, y⟩

instance has_uncurry_dep_induction [has_uncurry_dep γ β₁ β₂] : has_uncurry_dep (λ x, δ x → γ x) (λ x, δ x × β₁ x) β₂ :=
⟨λ x f p, ↾(f p.1) p.2⟩

end function

open_locale complexity_class
open function tencodable

namespace complexity_class

variables {α : Type} {β : α → Type} {β₁ : α → Type} {β₂ : α → Type} {γ δ : Type}
  [tencodable α] [∀ x, tencodable (β x)] [∀ x, tencodable (β₁ x)] [∀ x, tencodable (β₂ x)]
  [tencodable γ] [tencodable δ] {C : complexity_class}

/-- Membership of a dependent function in a complexity class;
  Note: we only ever need *one* dependent argument for almost everything we do
  
  TODO: can we unify `mem_dep` ("base case") and `mem_dep₂`?
  Can we and should we use has_uncurry_dep so that `mem_dep₂` is automatically
  generalized for >2 arguments?
  
  Should we generate composition lemmas for `mem_dep` and `mem_dep₂`? If so, what are they?  -/
def mem_dep (f : ∀ x, β x) (C : complexity_class) : Prop :=
∃ (f' : tree unit → tree unit), f' ∈ₑ C ∧
  ∀ x : α, f' (encode x) = encode (f x)

localized "infix ` ∈ₐ `:50 := complexity_class.mem_dep" in complexity_class

/-- `fintype` but "C"-constructible -/
def mem_types (β : α → Type) [∀ x, tencodable (β x)] [∀ x, decidable_eq (β x)]
  [∀ x, fintype (β x)] (C : complexity_class) : Prop :=
(λ x : α, @finset.univ (β x) _) ∈ₐ C

def mem_dep₂ (f : ∀ x, β₁ x → β₂ x) (C : complexity_class) : Prop :=
(λ x : sigma β₁, f x.1 x.2) ∈ₐ C

-- "t" for "two" ??
localized "infix ` ∈ₜ `:50 := complexity_class.mem_dep₂" in complexity_class
open_locale tree

@[simp] lemma mem_dep_iff {f : α → γ} : f ∈ₐ C ↔ f ∈ₑ C :=
by { simp_rw [mem_dep, ← prop_iff_mem], refl, }

lemma mem_dep₂_iff {f : α → γ → δ} : f ∈ₜ C ↔ f ∈ₑ C :=
by { dunfold mem_dep₂, rw mem_dep_iff, split; { rintro ⟨f', pf, hf⟩, refine ⟨f', pf, _⟩, rintro ⟨a, b⟩, exact hf ⟨a, b⟩, }, }

@[complexity] lemma mem_dep_of_mem {f : α → γ} (h : f ∈ₑ C) : f ∈ₐ C := by rwa mem_dep_iff
@[complexity] lemma mem_dep₂_of_mem {f : α → γ → δ} (h : f ∈ₑ C) : f ∈ₜ C := by rwa mem_dep₂_iff 

lemma mem_iff_comp_encode_dep {f : ∀ x, β x} :
  f ∈ₐ C ↔ (λ x, encode (f x)) ∈ₑ C :=
by { rw ← mem_dep_iff, refl, }

lemma _root_.list.encode_map_encode (l : list α) :
  encode (l.map encode) = encode l := by simp only [encode, list.map_id]

lemma mem_iff_comp_list_encode_dep {f : ∀ x, list (β x)} :
  f ∈ₐ C ↔ (λ x, (f x).map encode) ∈ₑ C :=
by { rw [mem_iff_comp_encode, mem_iff_comp_encode_dep], simp only [list.encode_map_encode], }

lemma _root_.tencodable.encode_sigma (x : α) (y : β x) : encode (⟨x, y⟩ : sigma β) = (encode x) △ (encode y) := rfl

end complexity_class

namespace polytime
open_locale complexity_class
open_locale tree
open complexity_class

variables {α : Type} {β : α → Type} {β₁ : α → Type} {β₂ : α → Type} {γ δ : Type}
  [tencodable α] [∀ x, tencodable (β x)] [∀ x, tencodable (β₁ x)] [∀ x, tencodable (β₂ x)]
  [tencodable γ] [tencodable δ] {C : complexity_class}

lemma list_map_dep {l : ∀ x, list (β₁ x)} {f : ∀ x, β₁ x → β₂ x} (hl : l ∈ₐ PTIME)
  (hf : f ∈ₜ PTIME) : (λ x : α, (l x).map (f x) : ∀ x, list (β₂ x)) ∈ₐ PTIME :=
begin
  rcases hf with ⟨f', pf, hf⟩,
  rw mem_iff_comp_list_encode_dep at ⊢ hl,
  complexity using λ x, ((l x).map encode).map (λ y, f' (encode x △ y)),
  simp at hf, dsimp [tencodable.encode_sigma] at hf, simp [function.comp, hf],
end



end polytime