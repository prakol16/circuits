import circuits.basic
import polytime.lemmas

open tencodable tree
open_locale tree complexity_class


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