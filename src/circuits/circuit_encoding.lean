import circuits.basic
import polytime.lemmas

open tencodable tree
open_locale tree complexity_class

section
variables {α : Type*} {β : α → Type*}

lemma multiset.nodupkeys_iff {s : multiset (sigma β)} :
  s.nodupkeys ↔ s.keys.nodup := quotient.induction_on s $ λ l, iff.rfl

lemma finmap.keysnodup (f : finmap β) : f.entries.keys.nodup := multiset.nodupkeys_iff.mp f.nodupkeys

def finmap.of_fun [fintype α] (f : Π x, β x) :
  finmap β :=
{ entries := finset.univ.val.map (λ x : α, ⟨x, f x⟩),
  nodupkeys := by simpa [multiset.nodupkeys_iff, multiset.keys] using finset.univ.nodup }

lemma finmap.mem_lookup_iff [decidable_eq α] {f : finmap β} {x : α} (y : β x) :
   f.lookup x = some y ↔ (⟨x, y⟩ : sigma β) ∈ f.entries :=
finmap.induction_on f (λ a, alist.mem_lookup_iff) 

@[simp] lemma finmap.of_fun_lookup [fintype α] [decidable_eq α] {f : Π x, β x} (x : α) :
  (finmap.of_fun f).lookup x = some (f x) :=
by { rw finmap.mem_lookup_iff, exact multiset.mem_map_of_mem _ (finset.mem_univ_val x), }

def finmap.comap {α β γ : Type*} (m : @finmap α (λ _, β)) (f : α ↪ γ) : @finmap γ (λ _, β) :=
{ entries := m.entries.map (λ x, ⟨f x.1, x.2⟩),
  nodupkeys := multiset.nodupkeys_iff.mpr (by simpa [multiset.keys] using m.keysnodup.map f.2) }

def finmap.disj_union {α β γ : Type*} (m₁ : @finmap α (λ _, γ)) (m₂ : @finmap β (λ _, γ)) : @finmap (α ⊕ β) (λ _, γ) :=
{ entries := m₁.entries.map (λ x, ⟨sum.inl x.1, x.2⟩) + m₂.entries.map (λ x, ⟨sum.inr x.1, x.2⟩),
  nodupkeys := begin
    rw [multiset.nodupkeys_iff, multiset.keys, multiset.map_add, multiset.nodup_add],
    refine ⟨_, _, _⟩,
    { simpa [multiset.keys] using m₁.keysnodup.map sum.inl_injective, },
    { simpa [multiset.keys] using m₂.keysnodup.map sum.inr_injective, },
    { simp [multiset.disjoint], }
  end }

@[simp] lemma finmap.disj_union_lookup_left {α β γ : Type*} [decidable_eq α] [decidable_eq β] (m₁ : @finmap α (λ _, γ)) (m₂ : @finmap β (λ _, γ)) (x : α) :
  (m₁.disj_union m₂).lookup (sum.inl x) = m₁.lookup x :=
by { ext y, simp [finmap.mem_lookup_iff, finmap.disj_union], }

@[simp] lemma finmap.disj_union_lookup_right {α β γ : Type*} [decidable_eq α] [decidable_eq β] (m₁ : @finmap α (λ _, γ)) (m₂ : @finmap β (λ _, γ)) (x : β) :
  (m₁.disj_union m₂).lookup (sum.inr x) = m₂.lookup x :=
by { ext y, simp [finmap.mem_lookup_iff, finmap.disj_union], }

def finmap.map {γ : α → Type*} (m : finmap β) (f : ∀ x, β x → γ x) : finmap γ :=
{ entries := m.entries.map (λ x, ⟨x.1, f x.1 x.2⟩),
  nodupkeys := by simpa [multiset.nodupkeys_iff, multiset.keys] using m.keysnodup }

end

variables {α β U V W X : Type}

def precircuit.to_finmap [fintype V] (cct : precircuit U V) : @finmap V (λ _, list (U ⊕ V)) :=
finmap.of_fun cct.deps

def precircuit.comp_finmap (c₁ : @finmap V (λ _, list (U ⊕ V))) (c₂ : @finmap X (λ _, list (W ⊕ X))) 
  (f : W → U ⊕ V) :
  @finmap (V ⊕ X) (λ _, list (U ⊕ V ⊕ X)) :=
(c₁.map $ λ v dv, dv.map (λ x, (equiv.sum_assoc U V X) (sum.inl x))).disj_union
(c₂.map $ λ x dx, dx.map (λ wx, (equiv.sum_assoc U V X) (wx.map f id)))

variables  [tencodable α] [tencodable β] [tencodable U] [tencodable V]
  [tencodable W] [tencodable X]

def flatten_finmap (f : @finmap V (λ _, list (U ⊕ V))) : @finmap (tree unit) (λ _, list (tree unit ⊕ tree unit)) :=
(f.map $ λ _ l, l.map $ sum.map encode encode).comap ⟨encode, encode_injective⟩

-- TODO: maybe try
-- pcct.to_finmap : precircuit U V → finmap V (list (U ⊕ V))
-- flatten : (finmap V (list U ⊕ V)) → finmap (tree unit) (list (tree unit) ⊕ (tree unit))
/-

polytime_dep₂ ((U : Type) → (V : Type) → M U V → N U V) → Prop where M and N are functorial in U and V


comp_finmap : finmap V (list U ⊕ V) → finmap X (list X ⊕ W) → (f : W → U ⊕ V) → finmap (V ⊕ X) (list (U ⊕ V ⊕ X))

WTS: mem (λ n, flatten (pcct₁ n).to_finmap) → mem (λ n, flatten (pcct₂ n).to_finmap) →
  (λ n, flatten ((pcct₁ n).comp (pcct₂ n)).to_finmap)

--> λ n, flatten (comp_finmap (pcct₁ n).to_finmap (pcct₂ n).to_finmap)

WTS: polytime.mem $ λ (c₁ : precircuit U V) (c₂ : precircuit U V), 

-/