import data.polynomial.eval
import tactic.expand_exists
import complexity_class.lemmas

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
  (∃ p : polynomial ℕ, ∀ x (m ≤ (n x).num_nodes), (f^[m] x).num_nodes ≤ p.eval x.num_nodes) →
  polytime (λ x, f^[(n x).num_nodes] x)

namespace polytime

theorem of_eq {f g : tree unit → tree unit} (hf : polytime f) (H : ∀ n, f n = g n) : polytime g :=
(funext H : f = g) ▸ hf

protected theorem const : ∀ (n : tree unit), polytime (λ _, n)
| tree.nil := nil
| (x △ y) := (const x).pair (const y)

protected theorem id : polytime (λ x, x) := prec nil left (⟨polynomial.X, λ x, by simp⟩)

theorem num_nodes_poly {f : tree unit → tree unit} (hf : polytime f) :
  ∃ p : polynomial ℕ, ∀ x, (f x).num_nodes ≤ p.eval x.num_nodes :=
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

def polytime : complexity_class :=
{ prop := tree.polytime,
  nil := tree.polytime.nil,
  left := tree.polytime.left,
  right := tree.polytime.right,
  id := tree.polytime.id,
  pair := λ f₁ f₂, tree.polytime.pair,
  comp := λ f₁ f₂, tree.polytime.comp,
  ite' := λ c f g, tree.polytime.ite }

open_locale complexity_class
localized "notation `P` := polytime" in complexity_class

@[simp] lemma tree.polytime_iff {f : tree unit → tree unit} :
  tree.polytime f ↔ f ∈ₑ P := @complexity_class.prop_iff_mem P f

@[complexity] lemma tree.polytime_of_polytime {f : tree unit → tree unit} (h : f ∈ₑ P) :
  tree.polytime f := by rwa tree.polytime_iff

class polycodable (α : Type) extends tencodable α :=
(poly [] : tencodable.decode α ∈ₑ P)

attribute [complexity] polycodable.poly

variables {α β : Type}

lemma polycodable.decode_num_nodes_le (α : Type) [polycodable α] :
  ∃ p : polynomial ℕ, ∀ x y, decode α x = some y → (encode y).num_nodes ≤ p.eval x.num_nodes :=
begin
  obtain ⟨p, hp⟩ := @tree.polytime.num_nodes_poly (λ x, encode (decode α x)) (by complexity),
  use p, intros x y h,
  specialize hp x,
  simp only [h, encode, of_option, num_nodes, zero_add] at hp,
  exact nat.le_of_succ_le hp,
end

instance : polycodable (tree unit) :=
⟨complexity_class.decode⟩

instance [polycodable α] : polycodable (option α) :=
⟨complexity_class.option_decode (polycodable.poly α)⟩

instance [polycodable α] [polycodable β] : polycodable (α ⊕ β) :=
⟨complexity_class.sum_decode (polycodable.poly α) (polycodable.poly β)⟩

instance [polycodable α] [polycodable β] : polycodable (α × β) :=
⟨complexity_class.prod_decode (polycodable.poly α) (polycodable.poly β)⟩

lemma polycodable.mem'_iff_mem [polycodable α] [tencodable β] {γ : Type} [has_uncurry γ α β] (f : γ) :
  f ∈ₛ P ↔ f ∈ₑ P := complexity_class.mem'_iff_mem_decode (polycodable.poly α) 

class polysize (α : Type*) [tencodable α] :=
(size : α → ℕ)
(upper [] : ∃ p : polynomial ℕ, ∀ x, size x ≤ p.eval (encode x).num_nodes)
(lower [] : ∃ p : polynomial ℕ, ∀ x, (encode x).num_nodes ≤ p.eval (size x))

lemma polysize.decode_upper (α : Type) [polycodable α] [polysize α] :
  ∃ p : polynomial ℕ, ∀ x y, decode α x = some y → polysize.size y ≤ p.eval x.num_nodes :=
begin
  obtain ⟨p, hp⟩ := polycodable.decode_num_nodes_le α,
  obtain ⟨q, hq⟩ := polysize.upper α,
  use q.comp p,
  intros x y h,
  rw [polynomial.eval_comp],
  exact (hq _).trans (q.eval_mono $ hp _ _ h),
end

open polysize
variables [tencodable α] [tencodable β]

instance : inhabited (polysize α) :=
⟨{ size := λ x, (encode x).num_nodes,
  upper := ⟨polynomial.X, by simp⟩,
  lower := ⟨polynomial.X, by simp⟩ }⟩

@[simps]
instance fintype.polysize [fintype α] : polysize α :=
{ size := λ _, 0,
  upper := ⟨0, λ x, zero_le'⟩,
  lower := ⟨polynomial.C ((@finset.univ α _).sup (λ x, (encode x).num_nodes)), 
    λ x, by { simp, exact finset.le_sup (finset.mem_univ x), }⟩ }

instance [polysize α] [polysize β] : polysize (α × β) :=
begin
  refine_struct { size := λ x : α × β, size x.1 + size x.2 },
  { cases upper α with p hp, cases upper β with q hq,
    use p + q, rintro ⟨x₁, x₂⟩,
    rw polynomial.eval_add,
    refine add_le_add ((hp _).trans $ p.eval_mono _) ((hq _).trans $ q.eval_mono _);
    simp [encode]; linarith only, },
  cases lower α with p hp, cases lower β with q hq,
  use p + q + 1, rintro ⟨x₁, x₂⟩,
  simp only [encode, num_nodes, polynomial.eval_add, polynomial.eval_one, add_le_add_iff_right],
  exact add_le_add ((hp _).trans $ p.eval_mono le_self_add)
    ((hq _).trans $ q.eval_mono le_add_self),
end

@[simp] lemma polysize.prod_size [polysize α] [polysize β]
  (x : α) (y : β) : size (x, y) = size x + size y := rfl

instance : polysize ℕ := default
instance : polysize (tree unit) := default

@[simp] lemma polysize_unary_nat (n : ℕ) : size n = n :=
by simp [polysize.size]

@[simp] lemma polysize_tree_unit (x : tree unit) : size x = x.num_nodes := rfl

def polysize_uniform [polysize α] [polysize β] (f : α → β → β) : Prop :=
∃ (p : polynomial ℕ), ∀ x y, size (f x y) ≤ size y + p.eval (size x)

theorem polysize_uniform.iterate [polysize α] [polysize β] {f : α → β → β} {n : α → ℕ}
  (hf : polysize_uniform f) (hn : ∃ p : polynomial ℕ, ∀ x, n x ≤ p.eval (size x)) :
    ∃ p : mv_polynomial (fin 2) ℕ, ∀ x y, size ((f x)^[n x] y) ≤ mv_polynomial.eval ![size x, size y] p :=
begin
  cases hn with p hn, cases hf with q hf,
  use (mv_polynomial.X 1 + (polynomial.to_mv 0 p) * (polynomial.to_mv 0 q) : mv_polynomial (fin 2) ℕ),
  intros x y, specialize hn x,
  have : ∀ n : ℕ, size ((f x)^[n] y) ≤ size y + n * (q.eval $ size x),
  { intro n, induction n with n ih, 
    { simp, },
    rw [iterate_succ_apply', nat.succ_mul, ← add_assoc],
    refine (hf x _).trans _,
    simpa using ih, },
  refine (this $ n x).trans _,
  simp, mono, exact zero_le',
end

lemma iterate_aux {α : Type} [polycodable α] [polysize α] (n : α → tree unit) (f : α → α) (hn : n ∈ₑ P)
  (hf : f ∈ₑ P) (H : ∃ p : polynomial ℕ, ∀ x (m ≤ (n x).num_nodes), size (f^[m] x) ≤ p.eval (size x)) :
  polytime.mem (λ x, f^[(n x).num_nodes] x) :=
begin
  -- TODO: Extract into definition (maybe?)
  -- A version of f and n which fail "safely" (i.e. if you input something that
  --  decodes to `none`, the output is `nil`)
  set f' : tree unit → tree unit := λ s, (encode $ (decode α s).map f).right,
  set n' : tree unit → tree unit := λ s, (encode $ (decode α s).map n).right,
  obtain ⟨pf', pn'⟩ : tree.polytime f' ∧ tree.polytime n' := by { split; dsimp [f', n'], complexity, },
  have H₁ : ∀ x y, decode α x = some y → (f' x = encode (f y) ∧ n' x = n y),
  { intros x y h, dsimp [f', n'], simp [h, encode], },
  have H₂ : ∀ x, decode α x = none → f' x = tree.nil ∧ n' x = tree.nil,
  { intros x h, dsimp [f', n'], simp [h, encode], },
  have H₃ : ∀ y, f' (encode y) = encode (f y) ∧ n' (encode y) = n y := λ y, H₁ (encode y) _ (tencodable.encodek _),
  have H₃i : ∀ y m, f'^[m] (encode y) = encode (f^[m] y),
  { intros y m, induction m with m ih, { simp, },  simp [function.iterate_succ', ih, (H₃ _).1], },
  have H₄ : ∀ x y m, decode α x = some y → (f'^[m + 1] x = encode (f^[m + 1] y)),
  { intros x y m h, simp [H₁ x y h, H₃i], },
  refine ⟨_, tree.polytime.prec pn' pf' _, _⟩, swap,
  { intro x, simp [(H₃ x).2, has_uncurry.uncurry, H₃i], },
  cases H with p H, cases polysize.lower α with l hl, cases polysize.decode_upper α with u hu, 
  use (polynomial.X + (l.comp $ p.comp u)),
  intros x m hm,
  cases m, { simp, },
  cases hd : decode α x with y, { exfalso, simpa [H₂ x hd] using hm, },
  simp only [H₄ _ _ m hd, (H₁ _ _ hd).2] at ⊢ hm,
  specialize H _ _ hm,
  simp only [polynomial.eval_add, polynomial.eval_X, polynomial.eval_comp],
  apply le_add_left,
  refine (hl _).trans (l.eval_mono $ H.trans $ p.eval_mono $ hu _ _ hd),
end

lemma iterate_aux' {α β : Type} [polycodable α] [polycodable β] [polysize α] [polysize β] {n : α → tree unit} {f : α → β → β} {g : α → β} (hn : n ∈ₑ polytime)
  (hf : f ∈ₑ polytime) (hg : g ∈ₑ polytime) 
  (hp : ∃ p : mv_polynomial (fin 2) ℕ, ∀ x y (m ≤ (decode ℕ (n x)).iget), size ((f x)^[m] y) ≤ mv_polynomial.eval ![size x, size y] p) :
  polytime.mem (λ x, (f x)^[(decode ℕ (n x)).iget] (g x)) :=
begin
  set f' := λ xy : α × β, (xy.1, f xy.1 xy.2),
  have pf' : f' ∈ₑ P := by { dsimp [f'], complexity, },
  have hf' : ∀ n x y, f'^[n] (x, y) = (x, (f x)^[n] y),
  { intros n x y, induction n with n ih generalizing y, { simp, }, { simp [ih], } }, 
  have := iterate_aux (λ xy, n (prod.fst xy)) f' (by complexity) pf' _,
  { convert (complexity_class.mem.snd.comp this).comp (polytime.id'.pair hg),
    ext x, generalize : g x = y, dsimp only [id, decode], simp [hf'], },
  cases hp with p hp,
  use (mv_polynomial.X 0 + p).to_polynomial,
  rintros ⟨x₁, x₂⟩ m hm,
  simp at hm ⊢,
  refine trans _ (mv_polynomial.le_to_polynomial_of_le_sum₂ _ _ _),
  simpa [hf'] using hp x₁ x₂ m hm,
end
