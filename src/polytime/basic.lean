import data.polynomial.eval
import tactic.expand_exists
import complexity_class.lemmas
import polytime.size

open tree tencodable function
open_locale tree

namespace tree

inductive polytime : (tree unit → tree unit) → Prop
| nil : polytime (λ _, nil)
| id' : polytime id
| left : polytime (λ x, x.left)
| right : polytime (λ x, x.right)
| pair {f₁ f₂} : polytime f₁ → polytime f₂ → polytime (λ x, (f₁ x) △ (f₂ x))
| comp {f₁ f₂} : polytime f₁ → polytime f₂ → polytime (f₁ ∘ f₂)
| ite {f g₁ g₂} : polytime f → polytime g₁ → polytime g₂ → polytime (λ x, if f x = nil then g₁ x else g₂ x)
| bounded_rec {f} : polytime f → polysize_fun (λ x : tree unit, f^[x.left.num_nodes] x.right) →
    polytime (λ x : tree unit, f^[x.left.num_nodes] x.right)

namespace polytime

theorem of_eq {f g : tree unit → tree unit} (hf : polytime f) (H : ∀ n, f n = g n) : polytime g :=
(funext H : f = g) ▸ hf

protected theorem const : ∀ (n : tree unit), polytime (λ _, n)
| tree.nil := nil
| (x △ y) := (const x).pair (const y)

-- TODO: how to do make original lemma protected?
protected lemma id : polytime (λ x, x) := id'

@[simp] lemma uncurry_unary {α β : Type*} (f : α → β) : ↿f = f := rfl

theorem num_nodes_poly {f : tree unit → tree unit} (hf : polytime f) :
  polysize_fun f :=
begin
  induction hf,
  case nil { use 0, simp, },
  case id' { use polynomial.X, simp, },
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
  case ite : f g₁ g₂ _ _ _ _ ih₁ ih₂ { exact polysize_fun.ite ih₁ ih₂, },
  case bounded_rec : _ _ H { exact H, }
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
localized "notation `PTIME` := polytime" in complexity_class

@[simp] lemma tree.polytime_iff {f : tree unit → tree unit} :
  tree.polytime f ↔ f ∈ₑ PTIME := @complexity_class.prop_iff_mem PTIME f

@[complexity] lemma tree.polytime_of_polytime {f : tree unit → tree unit} (h : f ∈ₑ PTIME) :
  tree.polytime f := by rwa tree.polytime_iff

class polycodable (α : Type) extends tencodable α :=
(poly [] : tencodable.decode α ∈ₑ PTIME)

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
  f ∈ₛ PTIME ↔ f ∈ₑ PTIME := complexity_class.mem'_iff_mem_decode (polycodable.poly α) 

open polysize
variables [tencodable α] [tencodable β]

@[complexity] lemma polytime.size_le {γ : Type} [has_uncurry γ α β] [polysize α] [polysize β] {f : γ} (hf : f ∈ₑ PTIME) :
  polysize_fun f :=
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

lemma nil_node_iterate (n : ℕ) (y : tree unit) : ((λ x, tree.nil △ x)^[n] y).num_nodes = y.num_nodes + n :=
by { induction n; simp [function.iterate_succ', *], refl, }

@[complexity] lemma num_nodes : (@tree.num_nodes unit) ∈ₑ PTIME :=
⟨_, (tree.polytime.bounded_rec (tree.polytime.pair tree.polytime.nil tree.polytime.id) (⟨polynomial.X, (λ x, by { simp [nil_node_iterate], rw add_comm, cases x; simp, })⟩)).comp (tree.polytime.pair tree.polytime.id tree.polytime.nil),
  λ x, by simp [encode_nat_eq_iterate]⟩

instance : polycodable ℕ :=
⟨complexity_class.some.comp polytime.num_nodes⟩

theorem iterate_aux {n : tree unit → ℕ} {f : tree unit → tree unit → tree unit} {st : tree unit → tree unit}
  (hn : n ∈ₑ PTIME) (hf : f ∈ₑ PTIME) (hst : st ∈ₑ PTIME)
  (hf' : polysize_fun (λ (n : ℕ) (x y : tree unit), (f x)^[n] y)) : (λ x, (f x)^[n x] (st x)) ∈ₑ PTIME :=
begin
  set F : tree unit → tree unit := λ x, x.left △ (f x.left x.right),
  have hF : tree.polytime F := by { dsimp [F], complexity, },
  have hF' : ∀ n x y, F^[n] (x △ y) = x △ ((f x)^[n] y),
  { intros n x y, induction n generalizing y; simp [F, *], }, 
  rcases hn with ⟨n', pn, hn⟩, rcases hst with ⟨st', pst, hst⟩,
  refine ⟨_, tree.polytime.right.comp ((tree.polytime.bounded_rec hF _).comp
    (tree.polytime.pair pn (tree.polytime.pair tree.polytime.id pst))), _⟩,
  swap, { intro x, simp only [encode_unit_tree] at hn hst, simp [hF', hn, hst], },
  cases hf' with p hp,
  use polynomial.X + p + 1,
  rintro (_|⟨⟨⟩, n, xy⟩), { simp, },
  have : ∀ x y, (F^[n.num_nodes] (x △ y)).num_nodes ≤
    x.num_nodes + (p.eval $ n.num_nodes + (x.num_nodes + y.num_nodes) + 1) + 1,
  { intros x y, rw hF', specialize hp (n.num_nodes, x, y), simp [has_uncurry.uncurry, add_assoc] at hp ⊢, refine hp.trans (p.eval_mono _), simp, },
  rcases xy with (_|⟨⟨⟩, x, y⟩),
  { simp, cases n.num_nodes with n, { simp, }, refine (this _ _).trans _, simp, },
  { refine (this _ _).trans _, simp [add_assoc x.num_nodes y.num_nodes 1],
    mono*, exacts [le_add_right $ le_add_left $ le_self_add, le_self_add], },
end

theorem iterate_safe_aux {n : tree unit → ℕ} {f : tree unit → tree unit → tree unit} {st : tree unit → tree unit}
  (hn : n ∈ₑ PTIME) (hf : f ∈ₑ PTIME) (hst : st ∈ₑ PTIME)
  (hf' : polysize_safe f) : (λ x, (f x)^[n x] (st x)) ∈ₑ PTIME :=
begin
  apply iterate_aux hn hf hst,
  use polynomial.X + polynomial.X * hf'.poly,
  rintros ⟨n, x, y⟩,
  refine (hf'.size_le n x y).trans _,
  simp [has_uncurry.uncurry], mono*,
  exacts [le_add_left le_add_self, le_self_add, le_add_left le_self_add, zero_le', zero_le'],
end

local attribute [complexity] iterate_safe_aux

@[complexity] lemma nat_add : ((+) : ℕ → ℕ → ℕ) ∈ₑ PTIME :=
by { complexity using λ m n, ((encode m) △ (encode n)).num_nodes.pred, simp, }

@[complexity] lemma nat_mul : ((*) : ℕ → ℕ → ℕ) ∈ₑ PTIME :=
begin
  refine ⟨λ x, ((λ acc : tree unit, encode (x.left.num_nodes + acc.num_nodes))^[x.right.num_nodes] tree.nil), by complexity, _⟩,
  rintro ⟨m, n⟩,
  suffices : ((λ acc, encode (m + acc.num_nodes))^[n] tree.nil) = encode (m * n), { simpa [encode_prod], },
  induction n with n ih, { simp [encode], },
  simp [iterate_succ_apply', ih, nat.mul_succ, add_comm],
end

lemma encode_pred (n : ℕ) : encode n.pred = (encode n).right :=
by { cases n; simp [encode], }

@[complexity] lemma nat_tsub : (has_sub.sub : ℕ → ℕ → ℕ) ∈ₑ PTIME :=
begin
  refine ⟨λ x, tree.right^[x.right.num_nodes] x.left, by complexity, _⟩,
  rintro ⟨m, n⟩,
  suffices : (tree.right^[n] (encode m)) = encode (m - n), { simpa [encode_prod], },
  induction n with n ih, { simp, }, { simp [iterate_succ_apply', ih, nat.sub_succ, encode_pred], }
end

/-- For any fixed polynomial `p`, `p.eval` runs in polynomial time -/
lemma polynomial_eval (p : polynomial ℕ) :
  polytime.mem (λ n : ℕ, p.eval n) :=
begin
  induction p using polynomial.induction_on with p p q ih₁ ih₂ p q ih,
  { simpa using polytime.const _, },
  { simpa using nat_add.comp₂ ih₁ ih₂, },
  simpa [pow_add, ← mul_assoc] using nat_mul.comp₂ ih polytime.id',
end

@[complexity] lemma polynomial_eval' (p : polynomial ℕ) {f : α → ℕ} (hf : f ∈ₑ PTIME) :
  polytime.mem (λ x, p.eval (f x)) := (polynomial_eval p).comp hf

@[complexity] lemma nat_le : polytime.mem_pred ((≤) : ℕ → ℕ → Prop) :=
by { complexity using (λ x y, x - y = 0), rw tsub_eq_zero_iff_le, }

@[complexity] lemma nat_lt : polytime.mem_pred ((<) : ℕ → ℕ → Prop) :=
by { complexity using (λ x y, x ≤ y ∧ ¬(y ≤ x)), rw lt_iff_le_not_le, }

/- Combining these allows us to iterate a function which automatically exits when it takes too long.
Thus, even on "bad" inputs, it does not take more than polynomial time. -/
def tree.guard_size (x : tree unit) (n : ℕ) : tree unit :=
if x.num_nodes ≤ n then x else tree.nil

@[complexity] lemma tree_guard_size : tree.guard_size ∈ₑ PTIME :=
by { delta tree.guard_size, complexity, }

lemma tree.guard_size_num_nodes_le (x : tree unit) (n) : (x.guard_size n).num_nodes ≤ n :=
by { simp only [tree.guard_size], split_ifs, { assumption, }, exact zero_le', }

lemma tree.guard_size_pos (x : tree unit) {n} (h : x.num_nodes ≤ n) : x.guard_size n = x :=
by rwa [tree.guard_size, if_pos]

local attribute [-complexity] iterate_safe_aux

theorem iterate_encode_size {n : α → ℕ} {f : α → β → β} {g : α → β} : n ∈ₑ PTIME → f ∈ₑ PTIME → g ∈ₑ PTIME → 
  (∃ p : polynomial ℕ, ∀ x (m ≤ n x), (encode $ (f x)^[m] (g x)).num_nodes ≤ p.eval (encode x).num_nodes) →
  polytime.mem (λ x, (f x)^[n x] (g x))
| ⟨n', pn, hn⟩ ⟨f', pf, hf⟩ ⟨g', pg, hg⟩ ⟨p, hp⟩ := begin
  refine ⟨λ x, (λ y, (f' (x △ y)).guard_size (p.eval $ x.num_nodes))^[(n' x).num_nodes] (g' x), _, _⟩,
  { rw [complexity_class.prop_iff_mem] at *, apply iterate_aux,
    { complexity, }, { complexity, }, { exact pg, },
    use p + polynomial.X,
    rintros ⟨(_|n), x, y⟩, { simp [has_uncurry.uncurry, ← add_assoc], },
    transitivity p.eval x.num_nodes,
    { simpa [-iterate_succ, iterate_succ_apply', has_uncurry.uncurry] using tree.guard_size_num_nodes_le _ _, },
    simp only [polynomial.eval_add, polynomial.eval_X],
    exact le_add_right (p.eval_mono $ le_add_left le_self_add), },
  intros x,
  dsimp only [has_uncurry.uncurry, id] at hn hf hg ⊢,
  simp only [prod.forall, encode_prod] at hf,
  simp only [hn, hg, encode_num_nodes],
  specialize hp x, revert hp, generalize : (n x) = M, intro hp,
  induction M with M ih, { simp, },
  specialize ih (λ m hm, hp m (nat.le_succ_of_le hm)), specialize hp _ rfl.le,
  simp only [iterate_succ_apply', ih, hf] at ⊢ hp,
  rwa tree.guard_size_pos,
end

theorem iterate [polysize α] [polysize β] {n : α → ℕ} {f : α → β → β} {g : α → β} (hn : n ∈ₑ PTIME)
  (hf : f ∈ₑ PTIME) (hg : g ∈ₑ PTIME) :
  (∃ p : polynomial ℕ, ∀ x (m ≤ n x), size ((f x)^[m] (g x)) ≤ p.eval (size x)) →
  polytime.mem (λ x, (f x)^[n x] (g x))
| ⟨p, hp⟩ :=
let ⟨q₁, hq₁⟩ := polysize.upper α, ⟨q₂, hq₂⟩ := polysize.lower β in
 iterate_encode_size hn hf hg ⟨q₂.comp (p.comp q₁),
 λ x m hm, by { simpa using (hq₂ _).trans (q₂.eval_mono $ (hp x m hm).trans $ p.eval_mono $ hq₁ _), }⟩

@[complexity] theorem iterate_safe [polysize α] [polysize β] {n : α → ℕ} {f : α → β → β} {g : α → β} (hn : n ∈ₑ PTIME)
  (hf : f ∈ₑ PTIME) (hg : g ∈ₑ PTIME) (hp : polysize_safe f) : polytime.mem (λ x, (f x)^[n x] (g x)) :=
let ⟨p₁, hp₁⟩ := polytime.size_le hg, ⟨p₂, hp₂⟩ := polytime.size_le hn in
iterate hn hf hg ⟨p₁ + p₂ * hp.poly, λ x m hm,
  (hp.size_le m x (g x)).trans (by { simp, mono*, exacts [hm.trans (hp₂ _), zero_le'], })⟩

end iterate

end polytime
