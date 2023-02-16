import complexity_class.lemmas

namespace function
/- Note that Lean fails to infer something like
(infer_instance : ∀ x : α, has_uncurry (list (β x) → list (β x) → list (β x)) _ _)
unless all the underscores are made explicit for some reason.
(infer_instance : ∀ x : α, has_uncurry (list (β x) → list (β x) → list (β x)) (list (β x) × list (β x)) (list $ β x))

This is why we make the following instances
-/
variables {α : Type*} {β β₁ β₂ γ δ : α → Type*}

class has_uncurry_dep_aux {α : Type*} (β : α → Type*) (β₁ β₂ : out_param (α → Type*)) :=
(uncurry : ∀ {x}, (β x) → ((β₁ x) → (β₂ x)))

instance has_uncurry_dep_aux_base : has_uncurry_dep_aux (λ x, (β₁ x → β₂ x)) β₁ β₂ := ⟨λ x y, y⟩

instance has_uncurry_dep_aux_ind [has_uncurry_dep_aux γ β₁ β₂] : has_uncurry_dep_aux (λ x, δ x → γ x) (λ x, δ x × β₁ x) β₂ :=
⟨λ x f p, has_uncurry_dep_aux.uncurry _ (f p.1) p.2⟩

class has_uncurry_dep {α : Type*} (β : α → Type*) {α' : out_param Type*} (γ : out_param (α' → Type*)) :=
(uncurry : (∀ x, (β x)) → ∀ x', (γ x'))

notation (name := uncurry_dep) `↿ₚ`:max x:max := has_uncurry_dep.uncurry x

instance has_uncurry_dep_base : has_uncurry_dep (λ x, β x) β := ⟨λ f x, f x⟩

instance has_uncurry_dep_base₂ [has_uncurry_dep_aux γ β₁ β₂] :
  has_uncurry_dep (λ x, γ x) (λ z : (Σ x, β₁ x), β₂ z.1) :=
⟨λ f x, (has_uncurry_dep_aux.uncurry _ (f x.1)) x.2⟩

end function

namespace complexity_class
open_locale complexity_class
open tencodable function

section dep
variables (C : complexity_class)
  {α α' α₁ α₂ : Type} {β β₁ β₂ γ δ : α → Type} {γ' : α' → Type}
  [tencodable α] [tencodable α₁] [tencodable α₂] [∀ x, tencodable (β x)] [∀ x, tencodable (β₁ x)]
  [∀ x, tencodable (β₁ x)] [∀ x, tencodable (β₂ x)] [∀ x, tencodable (γ x)] [∀ x, tencodable (δ x)]

def mem1_dep (f : ∀ x, β x) : Prop :=
∃ (f' : tree unit → tree unit), C.prop f' ∧ ∀ x : α, f' (encode x) = encode (f x)

def mem_dep [has_uncurry_dep γ' γ] (f : ∀ x, γ' x) (C : complexity_class) : Prop :=
C.mem1_dep ↿ₚf

@[simp] lemma mem_dep_iff₁ (f : α → α₁) :
  mem_dep f C ↔ mem f C := iff.rfl

@[simp] lemma mem_dep_iff₂ (f : α → α₁ → α₂) :
  mem_dep f C ↔ mem f C :=
by split; rintro ⟨f, pf, hf⟩; refine ⟨f, pf, _⟩; rintro ⟨a, b⟩; exact hf ⟨a, b⟩

localized "infix ` ∈ₐ `:50 := complexity_class.mem_dep" in complexity_class

lemma mem_iff_comp_encode_dep {f : ∀ x, β x} :
  f ∈ₐ C ↔ (λ x, encode (f x)) ∈ₑ C := iff.rfl

lemma mem_dep_iff_comp_eq_encode {f : ∀ x, β x} (g : ∀ x, β x → α₁)
  (hg : ∀ (x : α) (y : β x), encode (g x y) = encode y) :
  f ∈ₐ C ↔ (λ x, g x (f x)) ∈ₑ C :=
by { rw [mem_iff_comp_encode, mem_iff_comp_encode_dep], simp only [hg], }

lemma mem_iff_comp_list_map_dep {f : ∀ x, list (β x)} :
  f ∈ₐ C ↔ (λ x, (f x).map encode) ∈ₑ C :=
C.mem_dep_iff_comp_eq_encode (λ x (y : list (β x)), y.map encode) (λ x y, by simp only [encode, list.map_id])

end dep

/-- A function which is encoded as a table -/
structure complexity_class.table_fun (α β : Type*) :=
(to_fun : α → β)

namespace table_fun
variables {α β γ : Type*}

localized "infixr ` [→] `:25 := complexity_class.table_fun" in complexity_class

instance : has_coe_to_fun (α [→] β) (λ _, α → β) := ⟨table_fun.to_fun⟩

@[ext]
protected lemma ext : ∀ (f g : α [→] β), ⇑f = (by exact ⇑g) → f = g
| ⟨f⟩ ⟨g⟩ rfl := rfl

@[simp] lemma to_fun_eq_coe (f : α [→] β) : f.to_fun = ⇑f := rfl

@[simps]
def equiv_fun : (α [→] β) ≃ (α → β) := ⟨λ f, ⇑f, λ f, ⟨f⟩, λ f, by ext; refl, λ f, rfl⟩

@[simps]
def sum (f : α [→] γ) (g : β [→] γ) : α ⊕ β [→] γ := ⟨sum.elim ⇑f ⇑g⟩

@[simps]
def map (f : α [→] β) (g : β → γ) : α [→] γ := ⟨λ x, g (f x)⟩

@[simps]
def comp (f : α [→] β) (g : γ [→] α) : γ [→] β := ⟨λ x, f (g x)⟩

def finmap_equiv_fun [fintype α] [decidable_eq α] :
  {x : @finmap α (λ _, β) // ∀ k : α, k ∈ x} ≃ (α → β) :=
{ to_fun := λ f x, @option.get _ ((↑f : finmap _).lookup x) (finmap.lookup_is_some.mpr $ f.prop x),
  inv_fun := λ f, ⟨finmap.of_fun f, λ k, finmap.mem_iff.mpr ⟨_, finmap.of_fun_lookup k⟩⟩,
  left_inv := λ f, by { ext : 1, apply finmap.ext_lookup, simp, },
  right_inv := λ f, by { ext, simp, } } 

variables [tencodable α] [fintype α] [decidable_eq α] [tencodable β] [tencodable γ]

instance : tencodable (α [→] β) :=
tencodable.of_equiv _ (equiv_fun.trans finmap_equiv_fun.symm)

lemma encode_table_fun (f : α [→] β) : encode f = encode (finmap_equiv_fun.symm ⇑f) :=
rfl

end table_fun

end complexity_class
