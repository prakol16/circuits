import data.polynomial.eval
import tactic.expand_exists
import complexity_class.stack_rec
import polytime.size

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

open polysize
variables [tencodable α] [tencodable β]

lemma polytime.size_le {γ : Type} [has_uncurry γ α β] [polysize α] [polysize β] {f : γ} (hf : f ∈ₑ P) :
  ∃ p : polynomial ℕ, ∀ x, size (↿f x) ≤ p.eval (size x) :=
begin
  rcases hf with ⟨f', pf, hf⟩, cases polysize.upper β with u hu, cases polysize.lower α with l hl,
  obtain ⟨p, hp⟩ := pf.num_nodes_poly,
  use u.comp (p.comp l),
  intro x,
  refine (hu (↿f x)).trans _,
  simp [← hf],
  exact u.eval_mono ((hp _).trans $ p.eval_mono (hl _)),
end

lemma polycodable.decode_num_nodes_le (α : Type) [polycodable α] :
  ∃ p : polynomial ℕ, ∀ x y, decode α x = some y → (encode y).num_nodes ≤ p.eval x.num_nodes :=
let ⟨p, hp⟩ := @tree.polytime.num_nodes_poly (λ x, encode (decode α x)) (by complexity) in
  ⟨p, λ x y h, nat.le_of_succ_le (by simpa [h, encode, of_option] using hp x)⟩

namespace polytime

section iterate

/- Our goal in this section is to show that polynomial iteration runs
  in polynomial time, subject to constraints on the state size not blowing up.
  
  One issue that comes up is that our iteration `tree.polytime.prec` requires the
  function to run in polynomial time on *all* inputs, whereas in general, iterating
  some `f : α → α` should only require that `f` runs in polynomial time on valid encodings
  of `α`.
  
  We therefore extract this property, `has_iterate`, which states that we can do iteration when
  the internal state is `α`. We will show that in fact `has_iterate` is always true. This is
  because we can always check the size of the current state as we are running, and if it is too big,
  or if we've taken too many steps, we simply stop and output a garbage value (since the input must not have
  been a valid encoding). But in order to prove this, we will need the ability to do some iteration (e.g. comparing nat's,
  computing tree sizes). Thus, we have a bit of a chicken-egg problem, which is the purpose of having this definition. -/
-- private def has_iterate (α : Type) [tencodable α] : Prop :=
-- ∀ (n : α → tree unit) (f : α → α) (hn : n ∈ₑ P) (hf : f ∈ₑ P)
--   (H : ∃ p : polynomial ℕ, ∀ x (m ≤ (n x).num_nodes), (encode (f^[m] x)).num_nodes ≤ p.eval (encode x).num_nodes),
--   polytime.mem (λ x, f^[(n x).num_nodes] x)

/-- Here, we allow the input to the iteration to pass through a preprocessing stage `g` first -/
private def it (strict : bool) (α β : Type) [tencodable α] [tencodable β] : Prop :=
∀ (n : α → tree unit) (f : α → α) (g : β → α) 
  (hn : n ∈ₑ P) (hf : f ∈ₑ P) (hg : g ∈ₑ P)
  (H : ∃ p : polynomial ℕ, ∀ x (m ≤ (n x).num_nodes), (strict → x ∈ set.range g) → (encode (f^[m] x)).num_nodes ≤ p.eval (encode x).num_nodes),
  polytime.mem (λ x, f^[(n (g x)).num_nodes] (g x))

/-- As a first step, we show that all `polycodable` types can be iterated on. 
  We can do this by explicitly decoding and encoding at each step, so that weird things
  (which may take longer than polynomial time) do not happen on invalid inputs. -/
private lemma it_of_polycodable (α : Type) [polycodable α] : it ff α β :=
begin
  rintros n f g hn hf hg ⟨p, H⟩,
  refine (_ : polytime.mem (λ x, f^[(n x).num_nodes] x)).comp hg, clear hg,
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
  cases polycodable.decode_num_nodes_le α with u hu,
  refine ⟨polynomial.X + (p.comp u), λ x m hm, _⟩,
  cases m, { simp, },
  cases hd : decode α x with y, { exfalso, simpa [H₂ x hd] using hm, },
  simp only [H₄ _ _ m hd, (H₁ _ _ hd).2, polynomial.eval_add, polynomial.eval_X, polynomial.eval_comp] at ⊢ hm,
  exact le_add_left ((H _ _ hm bool.not_ff.elim).trans $ p.eval_mono $ hu _ _ hd),
end

variables [polysize α] [polysize β] {strict : bool}

/-- Similar to the basic `has_iterate` property, but we use `size` instead of `(encode x).num_nodes` -/
private lemma it₁ (hiter : it strict α β) 
  (n : α → tree unit) (f : α → α) (g : β → α) 
  (hn : n ∈ₑ P) (hf : f ∈ₑ P) (hg : g ∈ₑ P)
  (H : ∃ p : polynomial ℕ, ∀ x (m ≤ (n x).num_nodes), (strict → x ∈ set.range g) → size (f^[m] x) ≤ p.eval (size x)) :
  polytime.mem (λ x, f^[(n (g x)).num_nodes] (g x)) :=
begin
  apply hiter n f g hn hf hg,
  obtain ⟨⟨l, hl⟩, ⟨u, hu⟩, ⟨p, hp⟩⟩ := ⟨polysize.lower α, polysize.upper α, H⟩,
  refine ⟨l.comp (p.comp u), λ x m h hs, _⟩,
  simp only [polynomial.eval_comp],
  exact (hl _).trans (l.eval_mono $ (hp _ _ h hs).trans $ p.eval_mono $ hu _),
end

private lemma it₂ (hiter : it strict (α × β) α) {n : α → tree unit} {f : α → β → β} {g : α → β} (hn : n ∈ₑ polytime)
  (hf : f ∈ₑ polytime) (hg : g ∈ₑ polytime)
  (hp : ∃ p : mv_polynomial (fin 2) ℕ, ∀ x (m ≤ (n x).num_nodes), ∀ y, (strict → y = g x) → size ((f x)^[m] y) ≤ mv_polynomial.eval ![size x, size y] p) :
  polytime.mem (λ x, (f x)^[(n x).num_nodes] (g x)) :=
begin
  set f' := λ xy : α × β, (xy.1, f xy.1 xy.2),
  have hf' : ∀ n x y, f'^[n] (x, y) = (x, (f x)^[n] y),
  { intros n x y, induction n with n ih generalizing y, { simp, }, { simp [ih], } }, 
  have := it₁ hiter (λ xy, n (prod.fst xy)) f' (λ x, (x, g x)) (by complexity) (by complexity) (by complexity) _,
  { convert complexity_class.mem.snd.comp this, ext x, simp [hf'], },
  cases hp with p hp,
  use (mv_polynomial.X 0 + p).to_polynomial,
  rintros ⟨x₁, x₂⟩ m hm hs,
  simp at hm hs ⊢,
  refine trans _ (mv_polynomial.le_to_polynomial_of_le_sum₂ _ _ _),
  simpa [hf'] using hp x₁ m hm x₂ (λ H, (hs H).symm),
end

/-- The same as `it₂` but `n` is a function to `ℕ` now -/
private theorem it₃ (hiter : it strict (α × β) α) {n : α → ℕ} {f : α → β → β} {g : α → β} (hn : n ∈ₑ P)
  (hf : f ∈ₑ P) (hg : g ∈ₑ P) 
  (hp : ∃ p : mv_polynomial (fin 2) ℕ, ∀ x (m ≤ n x) y, (strict → y = g x) → size ((f x)^[m] y) ≤ mv_polynomial.eval ![size x, size y] p) :
  polytime.mem (λ x, (f x)^[n x] (g x)) :=
by have := it₂ hiter (complexity_class.encode.comp hn) hf hg _; simpa

/-- The condition on `f` is a "local" condition, rather than one involving the iteration of `f` -/
private lemma it₄ (hiter : it strict (α × β) α) {n : α → ℕ}
  {f : α → β → β} {g : α → β} (hn : n ∈ₑ P) (hf : f ∈ₑ P) (hg : g ∈ₑ P) 
  (hp : polysize_uniform f) : polytime.mem (λ x, (f x)^[n x] (g x)) :=
let ⟨p, H⟩ := hp.iterate (by simpa using polytime.size_le hn) in
  it₃ hiter hn hf hg ⟨p, λ x m hm y _, H x y m hm⟩

/-- We extract `it₄` on the case of polycodable states so that we can mark
  it to be used by automation in this section. -/
theorem iterate_uniform' {α β : Type} [polycodable α] [polycodable β] [polysize α] [polysize β]
  {n : α → ℕ} {f : α → β → β} {g : α → β} (hn : n ∈ₑ P) (hf : f ∈ₑ P) (hg : g ∈ₑ P) 
  (hp : polysize_uniform f) : polytime.mem (λ x, (f x)^[n x] (g x)) :=
it₄ (it_of_polycodable (α × β)) hn hf hg hp


local attribute [complexity] iterate_uniform'

lemma nil_node_iterate (n : ℕ) (y : tree unit) : ((λ x, tree.nil △ x)^[n] y).num_nodes = y.num_nodes + n :=
by { induction n; simp [function.iterate_succ', *], refl, }

/-- We can measure the number of nodes by iterating `nil △` `x.num_nodes` times -/
@[complexity] lemma num_nodes : (@tree.num_nodes unit) ∈ₑ P :=
⟨λ x, (λ y : tree unit, tree.nil △ y)^[x.num_nodes] tree.nil, 
begin
  rw [complexity_class.prop_iff_mem],
  apply it₂ (it_of_polycodable (tree unit × tree unit)), complexity,
  use mv_polynomial.X 1 + mv_polynomial.X 0,
  intros x m hm y _,
  simpa [nil_node_iterate] using hm,
end, λ x, by { rw [← encode_nat_eq_iterate], refl, }⟩

instance : polycodable ℕ :=
⟨complexity_class.some.comp polytime.num_nodes⟩

/- Thus, we have that `ℕ` is `polycodable` so we can iterate on `ℕ`.
  We may therefore prove basic functions (`+`, `*`, `≤`) are polytime.
  Note that `ℕ` is encoded in a unary fashion here.  -/

@[complexity] lemma add : polytime.mem ((+) : ℕ → ℕ → ℕ) :=
by { complexity using (λ x y, nat.succ^[y] x), { use 1, simp, }, simp [nat.succ_iterate], }

@[complexity] lemma mul : polytime.mem ((*) : ℕ → ℕ → ℕ) :=
begin
  complexity using (λ x y, (+x)^[y] 0),
  { use polynomial.X, rintros ⟨a, b⟩ y, simp, },
  induction y; simp [iterate_succ', nat.mul_succ, *, mul_comm],
end

/-- For any fixed polynomial `p`, `p.eval` runs in polynomial time -/
lemma polynomial_eval (p : polynomial ℕ) :
  polytime.mem (λ n : ℕ, p.eval n) :=
begin
  induction p using polynomial.induction_on with p p q ih₁ ih₂ p q ih,
  { simpa using polytime.const _, },
  { simpa using add.comp₂ ih₁ ih₂, },
  simpa [pow_add, ← mul_assoc] using mul.comp₂ ih polytime.id',
end

@[complexity] lemma polynomial_eval' (p : polynomial ℕ) {f : α → ℕ} (hf : f ∈ₑ P) :
  polytime.mem (λ x, p.eval (f x)) := (polynomial_eval p).comp hf

@[complexity] lemma pred : nat.pred ∈ₑ P :=
⟨_, tree.polytime.right, λ n, by cases n; refl⟩

@[complexity] lemma tsub : (@has_sub.sub ℕ _) ∈ₑ P :=
by { complexity using (λ x y, nat.pred^[y] x), { use 0, simpa using nat.pred_le, }, rw nat.pred_iterate, }

@[complexity] lemma nat_le : polytime.mem_pred ((≤) : ℕ → ℕ → Prop) :=
by { complexity using (λ x y, x - y = 0), rw tsub_eq_zero_iff_le, }

/- We now prove that `has_iterate` is unconditionally true. The crucial ingredients are:
  - We can evaluate polynomials in polynomial time
  - We can prove `tree.guard_size`, which is the identity on trees
    whose size is less than `n` but otherwise returns a constant garbage value (`nil`),
    runs in polynomial time.
  
Combining these allows us to iterate a function which automatically exits when it takes too long.
Thus, even on "bad" inputs, it does not take more than polynomial time.
-/

def tree.guard_size (x : tree unit) (n : ℕ) : tree unit :=
if x.num_nodes ≤ n then x else tree.nil

@[complexity] lemma tree_guard_size : tree.guard_size ∈ₑ P :=
by { delta tree.guard_size, complexity, }

lemma tree.guard_size_num_nodes_le (x : tree unit) (n) : (x.guard_size n).num_nodes ≤ n :=
by { simp only [tree.guard_size], split_ifs, { assumption, }, exact zero_le', }

lemma tree.guard_size_pos (x : tree unit) {n} (h : x.num_nodes ≤ n) : x.guard_size n = x :=
by rwa [tree.guard_size, if_pos]

private lemma has_iterate_all (α β : Type) [tencodable α] [tencodable β] : it tt α β :=
begin
  rintros n f g ⟨n', pn, hn⟩ ⟨f', pf, hf⟩ ⟨g', pg, hg⟩ ⟨p, H⟩,
  refine ⟨λ x, (λ s : tree unit, (f' s).guard_size (p.eval (g' x).num_nodes))^[(n' (g' x)).num_nodes] (g' x), _, λ x, _⟩,
  { rw [complexity_class.prop_iff_mem] at *, apply it₃ (it_of_polycodable (tree unit × tree unit)), 
    complexity,
    cases size_le pg with pg' hpg',
    use (mv_polynomial.X 1 + polynomial.to_mv 0 (p.comp pg')),
    intros x m _ y _, 
    cases m, { simp, },
    rw iterate_succ_apply',
    simpa using le_add_left ((tree.guard_size_num_nodes_le _ _).trans $ p.eval_mono $ hpg' x), },
  rw [hg, hn],
  dsimp [has_uncurry.uncurry],
  specialize H (g x), 
  simp only [coe_sort_tt, set.mem_range_self, forall_true_left] at H,
  revert H, clear hn, generalize : (n (g x)).num_nodes = N, intro H,
  induction N with N ih,
  { simp, },
  rw [iterate_succ_apply', ih (λ m hm, H m $ hm.trans N.le_succ), hf,
    tree.guard_size_pos, iterate_succ_apply'], { refl, },
  simpa [has_uncurry.uncurry, iterate_succ'] using H (N + 1) rfl.le,  
end

/- We now extract `it₃` and `it₄` in the general case unconditionally -/
theorem iterate {n : α → ℕ} {f : α → β → β} {g : α → β} (hn : n ∈ₑ P)
  (hf : f ∈ₑ P) (hg : g ∈ₑ P) :
  (∃ p : polynomial ℕ, ∀ x (m ≤ n x), size ((f x)^[m] (g x)) ≤ p.eval (size x)) →
  polytime.mem (λ x, (f x)^[n x] (g x))
| ⟨p, hp⟩ := it₃ (has_iterate_all _ _) hn hf hg ⟨polynomial.to_mv 0 p, by simpa using hp⟩

local attribute [-complexity] iterate_uniform'

@[complexity] theorem iterate_uniform {n : α → ℕ} {f : α → β → β} {g : α → β} (hn : n ∈ₑ P)
  (hf : f ∈ₑ P) (hg : g ∈ₑ P) (hp : polysize_uniform f) : polytime.mem (λ x, (f x)^[n x] (g x)) :=
it₄ (has_iterate_all _ _) hn hf hg hp

end iterate

section stack_rec



end stack_rec

end polytime

-- example (p q : Prop) (hp : ¬p) : p → q := by library_search

-- example : ¬(ff : Prop) := bool.not_ff

-- #check not.elim