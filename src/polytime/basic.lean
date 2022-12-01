import data.polynomial.eval
import encode

open tree tencodable function
open_locale tree

namespace tree

inductive polytime : (tree unit → tree unit) → Prop
| nil : polytime (λ _, nil)
| left : polytime (λ x, x.left)
| right : polytime (λ x, x.right)
| pair {f₁ f₂} : polytime f₁ → polytime f₂ → polytime (λ x, (f₁ x) △ (f₂ x))
| comp {f₁ f₂} : polytime f₁ → polytime f₂ → polytime (f₁ ∘ f₂)
| prec {n f} : polytime n → polytime f →
  -- Key condition: the growth of the output of `f` should be polynomially bounded
  (∃ P : polynomial ℕ, ∀ x (m ≤ (n x).num_nodes), (f^[m] x).num_nodes ≤ P.eval x.num_nodes) →
  polytime (λ x, f^[(n x).num_nodes] x)

namespace polytime

theorem of_eq {f g : tree unit → tree unit} (hf : polytime f) (H : ∀ n, f n = g n) : polytime g :=
(funext H : f = g) ▸ hf

protected theorem const : ∀ (n : tree unit), polytime (λ _, n)
| tree.nil := nil
| (x △ y) := (const x).pair (const y)

protected theorem id : polytime (λ x, x) := prec nil left (⟨polynomial.X, λ x, by simp⟩)

theorem num_nodes_poly {f : tree unit → tree unit} (hf : polytime f) :
  ∃ P : polynomial ℕ, ∀ x, (f x).num_nodes ≤ P.eval x.num_nodes :=
begin
  induction hf,
  case nil { use 0, simp, },
  case left { use polynomial.X, simpa using left_num_nodes_le, },
  case right { use polynomial.X, simpa using right_num_nodes_le, },
  case pair : f₁ f₂ _ _ ih₁ ih₂
  { rcases ih₁ with ⟨P₁, ih₁⟩, rcases ih₂ with ⟨P₂, ih₂⟩,
    use P₁ + P₂ + 1,
    intro x,
    simp, mono, },
  case comp : f₁ f₂ _ _ ih₁ ih₂ 
  { rcases ih₁ with ⟨P₁, ih₁⟩, rcases ih₂ with ⟨P₂, ih₂⟩,
    use P₁.comp P₂,
    intro x,
    simp only [comp_app, polynomial.eval_comp],
    exact (ih₁ _).trans (P₁.eval_mono (ih₂ x)), },
  case prec : n f _ _ H _ _
  { rcases H with ⟨Pb, hPb⟩,
    exact ⟨Pb, λ x, hPb x _ rfl.le⟩, }
end

protected theorem ite {f g₁ g₂} (hf : polytime f) (hg₁ : polytime g₁) (hg₂ : polytime g₂) :
  polytime (λ x, if f x = tree.nil then g₁ x else g₂ x) :=
(left.comp ((prec (hf.comp right) (pair (hg₂.comp right) right) begin
  obtain ⟨P, hP⟩ := hg₂.num_nodes_poly,
  use P + polynomial.X + 1,
  rintros x (_|m) _,
  { simpa using nat.le_succ_of_le le_add_self, },
  { rw [iterate_succ, comp_app, iterate_fixed],
    { simp only [polynomial.eval_X, num_nodes, polynomial.eval_one, comp_app, polynomial.eval_add], mono*, 
      { exact (hP _).trans (P.eval_mono $ right_num_nodes_le _), },
      exact right_num_nodes_le _, },
    { simp, } }
end).comp (pair hg₁ polytime.id))).of_eq
begin
  intro x, cases H : f x, { simp [H], },
  simp only [H, comp_app, tree.right, num_nodes, iterate_succ],
  rw iterate_fixed; simp,
end

end polytime

end tree

variables {α β γ γ₀ γ₁ γ₂ γ₃ γ₄ γ₅ γ₆ γ₇ : Type}
variables [tencodable α] [tencodable β]

def polytime1 (f : α → β) : Prop :=
∃ (f' : tree unit → tree unit), tree.polytime f' ∧ ∀ x : α, f' (encode x) = encode (f x)

/-- Polynomial time functions in many arguments -/
def polytime [has_uncurry γ α β] (f : γ) : Prop :=
polytime1 ↿f

def polytime_pred [has_uncurry γ α Prop] (f : γ) : Prop :=
polytime (λ x : α, @to_bool (↿f x) (classical.dec _))

@[simp] lemma polytime1_iff_polytime {f : α → β} : polytime1 f ↔ polytime f := iff.rfl

lemma polytime1_iff_polytime_pred {f : α → Prop} :
  polytime1 (λ x, @to_bool (f x) (classical.dec _)) ↔ polytime_pred f := iff.rfl

lemma polytime_iff_polytime_pred' {f : α → Prop} [decidable_pred f] :
  polytime (λ x, to_bool (f x)) ↔ polytime_pred f :=
by { convert polytime1_iff_polytime_pred, ext, congr, }

@[simp] lemma tree.polytime.iff_polytime {f : tree unit → tree unit} :
  tree.polytime f ↔ polytime f :=
⟨λ pf, ⟨f, pf, λ _, rfl⟩, λ ⟨f', pf, hf⟩, pf.of_eq hf⟩

namespace polytime

protected theorem id : polytime (@id α) :=
⟨_, tree.polytime.id, λ _, rfl⟩

protected theorem const (x : α) :
polytime (λ _ : β, x) := ⟨_, tree.polytime.const (encode x), λ _, rfl⟩

/-- A type is considered `polycodable` if the decoding function is
  polynomial time. -/
class polycodable (α : Type*) extends tencodable α :=
(prim [] : polytime (tencodable.decode α))

protected lemma some : polytime (@some α) :=
⟨_, tree.polytime.nil.pair tree.polytime.id, λ x, by simp [encode, has_uncurry.uncurry]⟩

instance : polycodable (tree unit) :=
{ prim := polytime.some }

instance : polycodable unit :=
{ prim := polytime.const _ }

variables [tencodable γ] [tencodable γ₀] [tencodable γ₁] [tencodable γ₂]
  [tencodable γ₃] [tencodable γ₄] [tencodable γ₅] [tencodable γ₆]

theorem comp {f : α → β} {g : γ → α} :
  polytime f → polytime g → polytime (λ x, f (g x))
| ⟨f', pf', hf'⟩ ⟨g', pg', hg'⟩ :=
⟨_, pf'.comp pg', λ x, by simp [hf', hg', has_uncurry.uncurry]⟩

theorem pair {f : α → β} {g : α → γ} : polytime f → polytime g → polytime (λ x, (f x, g x))
| ⟨f', pf', hf'⟩ ⟨g', pg', hg'⟩ :=
⟨_, pf'.pair pg', λ x, by simp [hf', hg', encode, has_uncurry.uncurry]⟩

theorem fst : polytime (@prod.fst α β) := ⟨_, tree.polytime.left, λ _, rfl⟩
theorem snd : polytime (@prod.snd α β) := ⟨_, tree.polytime.right, λ _, rfl⟩

protected lemma ite {P : α → Prop} [decidable_pred P] {f : α → β} {g : α → β} :
  polytime_pred P → polytime f → polytime g → polytime (λ x, if P x then f x else g x)
| ⟨P', pP, hP⟩ ⟨f', pf, hf⟩ ⟨g', pg, hg⟩ :=
⟨_, tree.polytime.ite pP pf pg, λ x, by by_cases P x; simp [*, encode, has_uncurry.uncurry]⟩

/- TODO: Autogenerate these lemmas; convert following to Lean code:
var subscript = n => String.fromCharCode(8320 + n);

var template = n =>
`theorem comp${subscript(n)} 
  {f : ${range(n).map(m => `γ${subscript(m)}`).join(" → ") + " → α"}} 
  ${range(n).map(m => `{g${subscript(m)} : β → γ${subscript(m)}}`).join(" ")}
  (hf : polytime f) ${range(n).map(m => `(hg${subscript(m)}: polytime hg${subscript(m)})`).join(" ")} :
  polytime (λ x, f ${range(n).map(m => `(g${subscript(m)} x)`).join(" ")}) :=
  hf.comp $ ${range(n).map(m => `hg${subscript(m)}`).join(".pair $ ")}`
 
var template_pred = n =>
`theorem comp${subscript(n)} 
  {f : ${range(n).map(m => `γ${subscript(m)}`).join(" → ") + " → Prop"}} 
  ${range(n).map(m => `{g${subscript(m)} : α → γ${subscript(m)}}`).join(" ")}
  (hf : polytime_pred f) ${range(n).map(m => `(hg${subscript(m)}: polytime g${subscript(m)})`).join(" ")} :
  polytime_pred (λ x, f ${range(n).map(m => `(g${subscript(m)} x)`).join(" ")}) :=
  hf.comp $ ${range(n).map(m => `hg${subscript(m)}`).join(".pair $ ")}`

 -/
theorem comp₂ 
  {f : γ₀ → γ₁ → α} 
  {g₀ : β → γ₀} {g₁ : β → γ₁}
  (hf : polytime f) (hg₀: polytime g₀) (hg₁: polytime g₁) :
  polytime (λ x, f (g₀ x) (g₁ x)) :=
  hf.comp $ hg₀.pair $ hg₁

theorem comp₃ 
  {f : γ₀ → γ₁ → γ₂ → α} 
  {g₀ : β → γ₀} {g₁ : β → γ₁} {g₂ : β → γ₂}
  (hf : polytime f) (hg₀: polytime g₀) (hg₁: polytime g₁) (hg₂: polytime g₂) :
  polytime (λ x, f (g₀ x) (g₁ x) (g₂ x)) :=
  hf.comp $ hg₀.pair $ hg₁.pair $ hg₂

theorem comp₄ 
  {f : γ₀ → γ₁ → γ₂ → γ₃ → α} 
  {g₀ : β → γ₀} {g₁ : β → γ₁} {g₂ : β → γ₂} {g₃ : β → γ₃}
  (hf : polytime f) (hg₀: polytime g₀) (hg₁: polytime g₁) (hg₂: polytime g₂) (hg₃: polytime g₃) :
  polytime (λ x, f (g₀ x) (g₁ x) (g₂ x) (g₃ x)) :=
  hf.comp $ hg₀.pair $ hg₁.pair $ hg₂.pair $ hg₃

theorem comp₅ 
  {f : γ₀ → γ₁ → γ₂ → γ₃ → γ₄ → α} 
  {g₀ : β → γ₀} {g₁ : β → γ₁} {g₂ : β → γ₂} {g₃ : β → γ₃} {g₄ : β → γ₄}
  (hf : polytime f) (hg₀: polytime g₀) (hg₁: polytime g₁) (hg₂: polytime g₂) (hg₃: polytime g₃) (hg₄: polytime g₄) :
  polytime (λ x, f (g₀ x) (g₁ x) (g₂ x) (g₃ x) (g₄ x)) :=
  hf.comp $ hg₀.pair $ hg₁.pair $ hg₂.pair $ hg₃.pair $ hg₄

theorem comp₆ 
  {f : γ₀ → γ₁ → γ₂ → γ₃ → γ₄ → γ₅ → α} 
  {g₀ : β → γ₀} {g₁ : β → γ₁} {g₂ : β → γ₂} {g₃ : β → γ₃} {g₄ : β → γ₄} {g₅ : β → γ₅}
  (hf : polytime f) (hg₀: polytime g₀) (hg₁: polytime g₁) (hg₂: polytime g₂) (hg₃: polytime g₃) (hg₄: polytime g₄) (hg₅: polytime g₅) :
  polytime (λ x, f (g₀ x) (g₁ x) (g₂ x) (g₃ x) (g₄ x) (g₅ x)) :=
  hf.comp $ hg₀.pair $ hg₁.pair $ hg₂.pair $ hg₃.pair $ hg₄.pair $ hg₅

theorem comp₇ 
  {f : γ₀ → γ₁ → γ₂ → γ₃ → γ₄ → γ₅ → γ₆ → α} 
  {g₀ : β → γ₀} {g₁ : β → γ₁} {g₂ : β → γ₂} {g₃ : β → γ₃} {g₄ : β → γ₄} {g₅ : β → γ₅} {g₆ : β → γ₆}
  (hf : polytime f) (hg₀: polytime g₀) (hg₁: polytime g₁) (hg₂: polytime g₂) (hg₃: polytime g₃) (hg₄: polytime g₄) (hg₅: polytime g₅) (hg₆: polytime g₆) :
  polytime (λ x, f (g₀ x) (g₁ x) (g₂ x) (g₃ x) (g₄ x) (g₅ x) (g₆ x)) :=
  hf.comp $ hg₀.pair $ hg₁.pair $ hg₂.pair $ hg₃.pair $ hg₄.pair $ hg₅.pair $ hg₆

end polytime

namespace polytime_pred
variables [tencodable γ] [tencodable γ₀] [tencodable γ₁] [tencodable γ₂]
  [tencodable γ₃] [tencodable γ₄] [tencodable γ₅] [tencodable γ₆]

theorem comp
  {f : γ₀ → Prop} 
  {g₀ : α → γ₀}
  (hf : polytime_pred f) (hg₀: polytime g₀) :
  polytime_pred (λ x, f (g₀ x)) :=
  hf.comp $ hg₀

theorem comp₂ 
  {f : γ₀ → γ₁ → Prop} 
  {g₀ : α → γ₀} {g₁ : α → γ₁}
  (hf : polytime_pred f) (hg₀: polytime g₀) (hg₁: polytime g₁) :
  polytime_pred (λ x, f (g₀ x) (g₁ x)) :=
  hf.comp $ hg₀.pair $ hg₁

theorem comp₃ 
  {f : γ₀ → γ₁ → γ₂ → Prop} 
  {g₀ : α → γ₀} {g₁ : α → γ₁} {g₂ : α → γ₂}
  (hf : polytime_pred f) (hg₀: polytime g₀) (hg₁: polytime g₁) (hg₂: polytime g₂) :
  polytime_pred (λ x, f (g₀ x) (g₁ x) (g₂ x)) :=
  hf.comp $ hg₀.pair $ hg₁.pair $ hg₂

theorem comp₄ 
  {f : γ₀ → γ₁ → γ₂ → γ₃ → Prop} 
  {g₀ : α → γ₀} {g₁ : α → γ₁} {g₂ : α → γ₂} {g₃ : α → γ₃}
  (hf : polytime_pred f) (hg₀: polytime g₀) (hg₁: polytime g₁) (hg₂: polytime g₂) (hg₃: polytime g₃) :
  polytime_pred (λ x, f (g₀ x) (g₁ x) (g₂ x) (g₃ x)) :=
  hf.comp $ hg₀.pair $ hg₁.pair $ hg₂.pair $ hg₃

theorem comp₅ 
  {f : γ₀ → γ₁ → γ₂ → γ₃ → γ₄ → Prop} 
  {g₀ : α → γ₀} {g₁ : α → γ₁} {g₂ : α → γ₂} {g₃ : α → γ₃} {g₄ : α → γ₄}
  (hf : polytime_pred f) (hg₀: polytime g₀) (hg₁: polytime g₁) (hg₂: polytime g₂) (hg₃: polytime g₃) (hg₄: polytime g₄) :
  polytime_pred (λ x, f (g₀ x) (g₁ x) (g₂ x) (g₃ x) (g₄ x)) :=
  hf.comp $ hg₀.pair $ hg₁.pair $ hg₂.pair $ hg₃.pair $ hg₄

end polytime_pred
