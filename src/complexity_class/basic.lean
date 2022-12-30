import encode

open tree tencodable function
open_locale tree

/-- A complexity class is a set of functions closed under some
  basic operations which essentially allow constant-time modifications -/
structure complexity_class :=
(prop : (tree unit → tree unit) → Prop)
(nil : prop (λ _, nil))
(left : prop (λ x, x.left))
(right : prop (λ x, x.right))
(id : prop (λ x, x))
(pair : ∀ {f₁ f₂}, prop f₁ → prop f₂ → prop (λ x, (f₁ x) △ (f₂ x)))
(comp : ∀ {f₁ f₂}, prop f₁ → prop f₂ → prop (f₁ ∘ f₂))
(ite' : ∀ {c f g}, prop c → prop f → prop g → prop (λ x, if c x = tree.nil then f x else g x))

namespace complexity_class

variables (C : complexity_class)
  {α β γ γ₀ γ₁ γ₂ γ₃ γ₄ γ₅ γ₆ γ₇ : Type}
variables [tencodable α] [tencodable β]

def mem1 (f : α → β) : Prop :=
∃ (f' : tree unit → tree unit), C.prop f' ∧ ∀ x : α, f' (encode x) = encode (f x)

/-- Many argument function is in `f` -/
def mem [has_uncurry γ α β] (f : γ) (C : complexity_class) : Prop :=
C.mem1 ↿f

def mem_pred [has_uncurry γ α Prop] (f : γ) (C : complexity_class) : Prop := 
C.mem (λ x : α, @to_bool (↿f x) (classical.dec _))

localized "infix ` ∈ₑ `:50 := complexity_class.mem" in complexity_class
localized "infix ` ∈ₚ `:50 := complexity_class.mem_pred" in complexity_class

protected theorem prop_const : ∀ (n : tree unit), C.prop (λ _, n)
| tree.nil := C.nil
| (x △ y) := C.pair (prop_const x) (prop_const y)

protected theorem const (x : α) : (λ _ : β, x) ∈ₑ C :=
⟨_, C.prop_const (encode x), λ _, rfl⟩

protected theorem const' (x : α) : const β x ∈ₑ C := C.const x

variable {C}

@[simp] lemma mem1_iff_mem {f : α → β} : C.mem1 f ↔ f ∈ₑ C := iff.rfl

private lemma mem_iff_mem_pred_aux {f : α → Prop} :
  (λ x, @to_bool (f x) (classical.dec _)) ∈ₑ C ↔ f ∈ₚ C := iff.rfl

lemma mem_iff_mem_pred {f : α → Prop} [decidable_pred f] :
  ((λ x, to_bool (f x)) ∈ₑ C) ↔ f ∈ₚ C :=
by { convert mem_iff_mem_pred_aux, ext, congr, }

private lemma mem_iff_mem_rel_aux {f : α → α → Prop} :
  ((λ x y, @to_bool (f x y) (classical.dec _))) ∈ₑ C ↔ f ∈ₚ C := iff.rfl

lemma mem_iff_mem_rel {f : α → α → Prop} [decidable_rel f] :
  ((λ x y, (f x y : bool))) ∈ₑ C ↔ f ∈ₚ C :=
by { convert mem_iff_mem_rel_aux, ext, congr, }

@[simp] lemma prop_iff_mem {f : tree unit → tree unit} :
  C.prop f ↔ f ∈ₑ C :=
⟨λ pf, ⟨f, pf, λ _, rfl⟩, λ ⟨f', pf, hf⟩, by { convert pf, ext x, exact (hf x).symm, }⟩

variables [tencodable γ] [tencodable γ₀] [tencodable γ₁] [tencodable γ₂]
  [tencodable γ₃] [tencodable γ₄] [tencodable γ₅] [tencodable γ₆]

theorem mem.comp {f : α → β} {g : γ → α} :
  f ∈ₑ C → g ∈ₑ C → (λ x, f (g x)) ∈ₑ C
| ⟨f', pf', hf'⟩ ⟨g', pg', hg'⟩ :=
⟨_, C.comp pf' pg', λ x, by simp [hf', hg', has_uncurry.uncurry]⟩

theorem mem.pair {f : α → β} {g : α → γ} : f ∈ₑ C → g ∈ₑ C → (λ x, (f x, g x)) ∈ₑ C
| ⟨f', pf', hf'⟩ ⟨g', pg', hg'⟩ :=
⟨_, C.pair pf' pg', λ x, by simp [hf', hg', encode, has_uncurry.uncurry]⟩

theorem mem.fst : @prod.fst α β ∈ₑ C := ⟨_, C.left, λ _, rfl⟩
theorem mem.snd : @prod.snd α β ∈ₑ C := ⟨_, C.right, λ _, rfl⟩

protected lemma mem_pred.ite {P : α → Prop} [decidable_pred P] {f : α → β} {g : α → β} :
  P ∈ₚ C → f ∈ₑ C → g ∈ₑ C → (λ x, if P x then f x else g x) ∈ₑ C
| ⟨P', pP, hP⟩ ⟨f', pf, hf⟩ ⟨g', pg, hg⟩ :=
⟨_, C.ite' pP pf pg, λ x, by by_cases P x; simp [*, encode, has_uncurry.uncurry]⟩

/- TODO: Autogenerate these lemmas; convert following to Lean code:
var subscript = n => String.fromCharCode(8320 + n);

var template = n =>
`theorem mem.comp${subscript(n)} 
  {f : ${range(n).map(m => `γ${subscript(m)}`).join(" → ") + " → α"}} 
  ${range(n).map(m => `{g${subscript(m)} : β → γ${subscript(m)}}`).join(" ")}
  (hf : f ∈ₑ C) ${range(n).map(m => `(hg${subscript(m)}: g${subscript(m)} ∈ₑ C)`).join(" ")} :
  (λ x, f ${range(n).map(m => `(g${subscript(m)} x)`).join(" ")}) ∈ₑ C :=
  hf.comp $ ${range(n).map(m => `hg${subscript(m)}`).join(".pair $ ")}`
 
var template_pred = n =>
`theorem mem_pred.comp${subscript(n)} 
  {f : ${range(n).map(m => `γ${subscript(m)}`).join(" → ") + " → Prop"}} 
  ${range(n).map(m => `{g${subscript(m)} : α → γ${subscript(m)}}`).join(" ")}
  (hf : f ∈ₚ C) ${range(n).map(m => `(hg${subscript(m)}: g${subscript(m)} ∈ₑ C)`).join(" ")} :
  (λ x, f ${range(n).map(m => `(g${subscript(m)} x)`).join(" ")}) ∈ₚ C :=
  hf.comp $ ${range(n).map(m => `hg${subscript(m)}`).join(".pair $ ")}`

 -/
section comp
theorem mem.comp₂ 
  {f : γ₀ → γ₁ → α} 
  {g₀ : β → γ₀} {g₁ : β → γ₁}
  (hf : f ∈ₑ C) (hg₀: g₀ ∈ₑ C) (hg₁: g₁ ∈ₑ C) :
  (λ x, f (g₀ x) (g₁ x)) ∈ₑ C :=
  hf.comp $ hg₀.pair $ hg₁
theorem mem.comp₃ 
  {f : γ₀ → γ₁ → γ₂ → α} 
  {g₀ : β → γ₀} {g₁ : β → γ₁} {g₂ : β → γ₂}
  (hf : f ∈ₑ C) (hg₀: g₀ ∈ₑ C) (hg₁: g₁ ∈ₑ C) (hg₂: g₂ ∈ₑ C) :
  (λ x, f (g₀ x) (g₁ x) (g₂ x)) ∈ₑ C :=
  hf.comp $ hg₀.pair $ hg₁.pair $ hg₂
theorem mem.comp₄ 
  {f : γ₀ → γ₁ → γ₂ → γ₃ → α} 
  {g₀ : β → γ₀} {g₁ : β → γ₁} {g₂ : β → γ₂} {g₃ : β → γ₃}
  (hf : f ∈ₑ C) (hg₀: g₀ ∈ₑ C) (hg₁: g₁ ∈ₑ C) (hg₂: g₂ ∈ₑ C) (hg₃: g₃ ∈ₑ C) :
  (λ x, f (g₀ x) (g₁ x) (g₂ x) (g₃ x)) ∈ₑ C :=
  hf.comp $ hg₀.pair $ hg₁.pair $ hg₂.pair $ hg₃
theorem mem.comp₅ 
  {f : γ₀ → γ₁ → γ₂ → γ₃ → γ₄ → α} 
  {g₀ : β → γ₀} {g₁ : β → γ₁} {g₂ : β → γ₂} {g₃ : β → γ₃} {g₄ : β → γ₄}
  (hf : f ∈ₑ C) (hg₀: g₀ ∈ₑ C) (hg₁: g₁ ∈ₑ C) (hg₂: g₂ ∈ₑ C) (hg₃: g₃ ∈ₑ C) (hg₄: g₄ ∈ₑ C) :
  (λ x, f (g₀ x) (g₁ x) (g₂ x) (g₃ x) (g₄ x)) ∈ₑ C :=
  hf.comp $ hg₀.pair $ hg₁.pair $ hg₂.pair $ hg₃.pair $ hg₄
theorem mem.comp₆ 
  {f : γ₀ → γ₁ → γ₂ → γ₃ → γ₄ → γ₅ → α} 
  {g₀ : β → γ₀} {g₁ : β → γ₁} {g₂ : β → γ₂} {g₃ : β → γ₃} {g₄ : β → γ₄} {g₅ : β → γ₅}
  (hf : f ∈ₑ C) (hg₀: g₀ ∈ₑ C) (hg₁: g₁ ∈ₑ C) (hg₂: g₂ ∈ₑ C) (hg₃: g₃ ∈ₑ C) (hg₄: g₄ ∈ₑ C) (hg₅: g₅ ∈ₑ C) :
  (λ x, f (g₀ x) (g₁ x) (g₂ x) (g₃ x) (g₄ x) (g₅ x)) ∈ₑ C :=
  hf.comp $ hg₀.pair $ hg₁.pair $ hg₂.pair $ hg₃.pair $ hg₄.pair $ hg₅

theorem mem_pred.comp
  {f : γ₀ → Prop} 
  {g₀ : α → γ₀}
  (hf : f ∈ₚ C) (hg₀: g₀ ∈ₑ C) :
  (λ x, f (g₀ x)) ∈ₚ C :=
  hf.comp $ hg₀
theorem mem_pred.comp₂ 
  {f : γ₀ → γ₁ → Prop} 
  {g₀ : α → γ₀} {g₁ : α → γ₁}
  (hf : f ∈ₚ C) (hg₀: g₀ ∈ₑ C) (hg₁: g₁ ∈ₑ C) :
  (λ x, f (g₀ x) (g₁ x)) ∈ₚ C :=
  hf.comp $ hg₀.pair $ hg₁
theorem mem_pred.comp₃ 
  {f : γ₀ → γ₁ → γ₂ → Prop} 
  {g₀ : α → γ₀} {g₁ : α → γ₁} {g₂ : α → γ₂}
  (hf : f ∈ₚ C) (hg₀: g₀ ∈ₑ C) (hg₁: g₁ ∈ₑ C) (hg₂: g₂ ∈ₑ C) :
  (λ x, f (g₀ x) (g₁ x) (g₂ x)) ∈ₚ C :=
  hf.comp $ hg₀.pair $ hg₁.pair $ hg₂
theorem mem_pred.comp₄ 
  {f : γ₀ → γ₁ → γ₂ → γ₃ → Prop} 
  {g₀ : α → γ₀} {g₁ : α → γ₁} {g₂ : α → γ₂} {g₃ : α → γ₃}
  (hf : f ∈ₚ C) (hg₀: g₀ ∈ₑ C) (hg₁: g₁ ∈ₑ C) (hg₂: g₂ ∈ₑ C) (hg₃: g₃ ∈ₑ C) :
  (λ x, f (g₀ x) (g₁ x) (g₂ x) (g₃ x)) ∈ₚ C :=
  hf.comp $ hg₀.pair $ hg₁.pair $ hg₂.pair $ hg₃
theorem mem_pred.comp₅ 
  {f : γ₀ → γ₁ → γ₂ → γ₃ → γ₄ → Prop} 
  {g₀ : α → γ₀} {g₁ : α → γ₁} {g₂ : α → γ₂} {g₃ : α → γ₃} {g₄ : α → γ₄}
  (hf : f ∈ₚ C) (hg₀: g₀ ∈ₑ C) (hg₁: g₁ ∈ₑ C) (hg₂: g₂ ∈ₑ C) (hg₃: g₃ ∈ₑ C) (hg₄: g₄ ∈ₑ C) :
  (λ x, f (g₀ x) (g₁ x) (g₂ x) (g₃ x) (g₄ x)) ∈ₚ C :=
  hf.comp $ hg₀.pair $ hg₁.pair $ hg₂.pair $ hg₃.pair $ hg₄
theorem mem_pred.comp₆ 
  {f : γ₀ → γ₁ → γ₂ → γ₃ → γ₄ → γ₅ → Prop} 
  {g₀ : α → γ₀} {g₁ : α → γ₁} {g₂ : α → γ₂} {g₃ : α → γ₃} {g₄ : α → γ₄} {g₅ : α → γ₅}
  (hf : f ∈ₚ C) (hg₀: g₀ ∈ₑ C) (hg₁: g₁ ∈ₑ C) (hg₂: g₂ ∈ₑ C) (hg₃: g₃ ∈ₑ C) (hg₄: g₄ ∈ₑ C) (hg₅: g₅ ∈ₑ C) :
  (λ x, f (g₀ x) (g₁ x) (g₂ x) (g₃ x) (g₄ x) (g₅ x)) ∈ₚ C :=
  hf.comp $ hg₀.pair $ hg₁.pair $ hg₂.pair $ hg₃.pair $ hg₄.pair $ hg₅
end comp

theorem mem.swap_args₂ {f : α → β → γ} : f ∈ₑ C ↔ (flip f) ∈ₑ C :=
by { split; intro h; exact h.comp₂ mem.snd mem.fst, }

end complexity_class
