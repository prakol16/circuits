import complexity_class.lemmas
import data.multiset.functor
import data.finset.functor

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

section functor

class is_encodable_functor (F : Type → Type) [functor F] :=
(inst : ∀ x, tencodable x → tencodable (F x))
(map_encode : ∀ {α} [I : tencodable α] (x : F α), (@encode _ (inst _ infer_instance) $ @encode _ I <$> x) = @encode _ (inst _ I) x)

instance : is_encodable_functor list :=
⟨@list.tencodable, λ α _ x, by simp [encode]⟩

lemma list_map_encode (x : list α) : encode (x.map encode) = encode x := is_encodable_functor.map_encode x

instance : is_encodable_functor option :=
⟨@option.tencodable, λ α _ x, by cases x; simp [encode]⟩

lemma option_map_encode (x : option α) : encode (x.map encode) = encode x := is_encodable_functor.map_encode x

lemma _root_.list.sorted_map {α β : Type*} {r : β → β → Prop} (f : α → β) {l : list α} :
  (l.map f).sorted r ↔ l.sorted (λ x y, r (f x) (f y)) := list.pairwise_map f

lemma _root_.list.map_merge_sort {α β : Type*} (r : β → β → Prop) [decidable_rel r]
  [is_total β r] [is_trans β r] [is_antisymm β r] (f : α → β) (l : list α)  :
  (l.map f).merge_sort r = (l.merge_sort (λ x y, r (f x) (f y))).map f :=
begin
  refine list.eq_of_perm_of_sorted (trans ((l.map f).perm_merge_sort r) ((l.perm_merge_sort (λ x y, r (f x) (f y))).map f).symm)
    (list.sorted_merge_sort _ _) ((list.sorted_map f).mpr $ _),
  refine @list.sorted_merge_sort _ _ _ ⟨_⟩ ⟨_⟩ _,
  { intros a b, exact is_total.total (f a) (f b), },
  { intros a b c, exact is_trans.trans (f a) (f b) (f c), }
end

instance : is_encodable_functor multiset :=
⟨@multiset.tencodable, λ α _ x, quotient.induction_on x $ λ x, begin
  dsimp [encode_multiset, lift_le],
  rw [← @list_map_encode α, list.map_merge_sort],
end⟩

lemma multiset_map_encode (x : multiset α) : encode (x.map encode) = encode x := is_encodable_functor.map_encode x

section
open_locale classical

lemma _root_.finset.fmap_def' {α β : Type*} [decidable_eq β] (f : α → β) (x : finset α) :
  f <$> x = x.image f := by { dsimp, congr, }

noncomputable instance : is_encodable_functor finset :=
⟨λ α I, @finset.tencodable _ I _, λ α _ x, begin
  resetI,
  simp only [finset.fmap_def'],
  rw (show x.image encode = _, from (finset.map_eq_image ⟨encode, encode_injective⟩ x).symm),
  cases x with v hv,
  simp only [finset.map, encode_finset],
  exact multiset_map_encode _,
end⟩

lemma finset_image_encode [decidable_eq α] (x : finset α) : encode (x.image encode) = encode x := by convert is_encodable_functor.map_encode x

end

lemma functor_map_dep (F : Type → Type) [functor F] [is_lawful_functor F] [is_encodable_functor F]
  {l : ∀ x, F (β x)} {g : ∀ x, β x → γ x} (hl : by { haveI : ∀ x, tencodable (F (β x)) := λ x, is_encodable_functor.inst _ infer_instance, exact l ∈ₐ C, })
  (hg : g ∈ₐ C) (hm : by { haveI : tencodable (F (tree unit)) := is_encodable_functor.inst _ infer_instance,
    exact ∀ {l' : α → F (tree unit)} {g' : α → tree unit → tree unit}, l' ∈ₑ C → g' ∈ₑ C → (λ z, (g' z) <$> (l' z)) ∈ₑ C, }) :
  by { haveI : ∀ x, tencodable (F (γ x)) := λ x, is_encodable_functor.inst _ infer_instance, exact (λ x, (g x) <$> (l x)) ∈ₐ C } :=
begin
  letI : ∀ x, tencodable (F (β x)) := λ x, is_encodable_functor.inst _ infer_instance,
  letI : tencodable (F (tree unit)) := is_encodable_functor.inst _ infer_instance,
  letI : ∀ x, tencodable (F (γ x)) := λ x, is_encodable_functor.inst _ infer_instance,
  rcases hg with ⟨g', pg, hg⟩,
  simp only [sigma.forall] at hg,
  dsimp [encode_sigma, has_uncurry_dep.uncurry, has_uncurry_dep_aux.uncurry] at hg,
  rw C.mem_dep_iff_comp_eq_encode (λ x (y : F (γ x)), encode <$> y) (λ x y, is_encodable_functor.map_encode y),
  rw C.mem_dep_iff_comp_eq_encode (λ x (y : F (β x)), encode <$> y) (λ x y, is_encodable_functor.map_encode y) at hl,
  have pg' : (λ (x : α) (t : tree unit), g' (tree.node () (encode x) t)) ∈ₑ C := by complexity,
  convert hm hl pg',
  funext x,
  simp [functor.map_map, function.comp, hg],
end

end functor

-- lemma mem_iff_comp_list_map_dep {f : ∀ x, list (β x)} :
--   f ∈ₐ C ↔ (λ x, (f x).map encode) ∈ₑ C :=
-- C.mem_dep_iff_comp_eq_encode (λ x (y : list (β x)), y.map encode) (λ (x : α) y, list_map_encode y)

end dep

/-- A function which is encoded as a table -/
structure table_fun (α β : Type*) :=
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

def to_finmap [fintype α] (f : α [→] β) : @finmap α (λ _, β) := finmap.of_fun f 

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

open_locale complexity_class
variables {C : complexity_class} {α : Type} {β γ : α → Type} [tencodable α]
  [∀ i, tencodable (β i)] [∀ i, tencodable (γ i)] [∀ i, decidable_eq (β i)] [∀ i, fintype (β i)]

lemma to_finmap_iff {f : ∀ x, (β x) [→] (γ x)} : 
  f ∈ₐ C ↔ (λ x, (f x).to_finmap) ∈ₐ C := iff.rfl

@[complexity] lemma to_finmap {f : ∀ x, (β x) [→] (γ x)} (hf : f ∈ₐ C) : (λ x, (f x).to_finmap) ∈ₐ C := hf

end complexity_class
