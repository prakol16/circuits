import polytime.size
import stack_rec
import misc

open tree function polysize (size)
open_locale tree

namespace tree

section

variables {α : Type} {β : Type} [tencodable α] [tencodable β]
  {base : α → β} {pre₁ pre₂ : tree unit → tree unit → α → α}
  {post : β → β → tree unit → tree unit → α → β}

@[elab_as_eliminator]
theorem stack_step_induction
  (P : tree unit → α → iterator_stack α β → Prop)
  (hb : ∀ t arg, P t arg (sum.inl (t, arg, none))) 
  (hb' : ∀ ⦃l r arg res⦄, res = stack_rec base pre₁ pre₂ post l (pre₁ l r arg) → P l (pre₁ l r arg) (sum.inr res)
           → P (l △ r) arg (sum.inl (l △ r, arg, some res)))
  (hbr : ∀ arg, P tree.nil arg (sum.inr (base arg))) 
  (hi₁ : ∀ ⦃l r arg e⦄, P l (pre₁ l r arg) e → P (l △ r) arg e)
  (hi₂ : ∀ ⦃l r arg e⦄, P r (pre₂ l r arg) e → P (l △ r) arg e)
  (hp : ∀ ⦃l r arg res₁ res₂⦄,
    res₁ = stack_rec base pre₁ pre₂ post l (pre₁ l r arg) →
    res₂ = stack_rec base pre₁ pre₂ post r (pre₂ l r arg) →
    P l (pre₁ l r arg) (sum.inr res₁) →
    P r (pre₂ l r arg) (sum.inr res₂) →
    P (l △ r) arg (sum.inr $ post res₁ res₂ l r arg))
  :
  ∀ (x : tree unit) (arg : α) (n : ℕ)
    (e : iterator_stack α β) (he : e ∈ ((stack_step base pre₁ pre₂ post)^[n] [sum.inl (x, arg, none)])),
    P x arg e :=
begin
  -- For the inductive hypothesis, we add an excess `xs`
  suffices : ∀ (xs : list (iterator_stack α β)) (x : tree unit) (arg : α) (n : ℕ) (hn : n ≤ x.time_steps)
    (e : iterator_stack α β) (he : e ∈ ((stack_step base pre₁ pre₂ post)^[n] (sum.inl (x, arg, none) :: xs))),
    P x arg e ∨ e ∈ xs,
  { intros x arg n e he, refine (this [] x arg (min n x.time_steps) (min_le_right _ _) e _).resolve_right not_false, rwa stack_step_iterate_min, },
  intros,
  induction x using tree.unit_rec_on with l r ih₁ ih₂ generalizing arg xs n e,
  -- In the case `n=0`, no iteration happens, so the only
  -- nontrivial possibility is `e = sum.inl (t, arg, none)` (the base case)
  all_goals { cases n, { refine or.imp_left _ he, rintro rfl, exact hb _ arg, }, },
  { obtain rfl : n = 0 := by simpa [nat.succ_eq_add_one] using hn,
    refine or.imp_left _ he, rintro rfl, exact hbr arg, },
  -- In the inductive step, suppose we take `n+1` steps; we first show that `P` is true of the previous results (used several times later)
  have P_l_res : P l (pre₁ l r arg) (sum.inr $ stack_rec base pre₁ pre₂ post l (pre₁ l r arg)),
  { refine (ih₁ _ [] _ _ rfl.le _).resolve_right not_false, simp, },
  have P_r_res : P r (pre₂ l r arg) (sum.inr $ stack_rec base pre₁ pre₂ post r (pre₂ l r arg)),
  { refine (ih₂ _ [] _ _ rfl.le _).resolve_right not_false, simp, },
  -- Now we consider intermediate stages `0 ≤ n ≤ l.time_steps`
  by_cases H : n ≤ l.time_steps,
  { clear ih₂, rcases ih₁ (pre₁ l r arg) _ n e H he with (ih|rfl|ih),
    { left, exact hi₁ ih, }, { left, exact hb _ _, }, { right, exact ih, } },
  -- Now we consider the cases `n = l.time_steps + 1` i.e. `c=1` letting `c = n - l.time_steps`
  rcases lt_iff_exists_add.mp (lt_of_not_le H) with ⟨c, hc, rfl⟩, clear H,
  rw [iterate_succ_apply, add_comm l.time_steps, iterate_add_apply, stack_step, stack_step_iterate] at he,
  cases c, { cases not_lt_zero' hc, }, clear hc,
  cases c, { refine or.imp_left _ he, rintro rfl, exact hb' rfl P_l_res, },
  -- Next, we consider the cases `l.time_steps + 2 ≤ n ≤ l.time_steps + 2 + r.time_steps`
  by_cases H : c ≤ r.time_steps,
  { rcases ih₂ (pre₂ l r arg) _ c e H he with (ih|rfl|ih),
    { left, exact hi₂ ih, }, { left, exact hb' rfl P_l_res, }, { right, exact ih, }, },
  -- Finally, we consider the last step `n = l.time_steps + 2 + r.time_steps + 1`
  obtain rfl : c = 1 + r.time_steps,
  { simp [time_steps_node, nat.succ_eq_add_one] at hn, 
    linarith only [H, hn], },
  simp [iterate_add] at he,
  refine he.imp_left _, rintro rfl,
  exact hp rfl rfl P_l_res P_r_res,
end

-- First we show the length is bounded
-- Note this is inefficient because it does branching in many cases where we do not need to branch
lemma stack_step_len_le (ls : list (iterator_stack α β)) :
  (stack_step base pre₁ pre₂ post ls).length ≤ ls.length + 1 :=
by rcases ls with (_|⟨(⟨(_|⟨⟨⟩, l, r⟩), arg, (_|_)⟩|res), (_|⟨(⟨_,_,(_|_)⟩|_), _⟩)⟩); simp [add_assoc]

lemma stack_step_iter_len_le (ls : list (iterator_stack α β)) (n : ℕ) :
  ((stack_step base pre₁ pre₂ post)^[n] ls).length ≤ ls.length + n :=
by { induction n with n ih, { refl, }, rw [iterate_succ_apply'], exact (stack_step_len_le _).trans (nat.succ_le_succ ih), }

lemma stack_step_iter_len_le' (x : tree unit) (arg : α) (n : ℕ) :
  ((stack_step base pre₁ pre₂ post)^[n] [sum.inl (x, arg, none)]).length ≤ x.time_steps + 1 :=
by { rw [← stack_step_iterate_min, add_comm x.time_steps], refine (stack_step_iter_len_le _ _).trans _, simp, }

variables [polysize α] [polysize β] (bb bpr₁ bpr₂ bpo : polynomial ℕ)
  (hbb : ∀ x, size (base x) ≤ bb.eval (size x))
  (hbpr₁ : ∀ x y a, size (pre₁ x y a) ≤ (size a) + bpr₁.eval (size (x △ y)))
  (hbpr₂ : ∀ x y a, size (pre₂ x y a) ≤ (size a) + bpr₂.eval (size (x △ y)))
  (hbpo : ∀ ih₁ ih₂ x y a, size (post ih₁ ih₂ x y a) ≤ (size ih₁) + (size ih₂) + bpo.eval (size (x △ y, a)))

def max_arg_size (x₀ : tree unit) (arg₀ : α) : ℕ :=
size arg₀ + x₀.height * ((bpr₁.eval x₀.num_nodes) + (bpr₂.eval x₀.num_nodes))

def max_res_size (x₀ : tree unit) (arg₀ : α) : ℕ :=
x₀.num_leaves * bb.eval (max_arg_size bpr₁ bpr₂ x₀ arg₀) + x₀.num_nodes * bpo.eval (x₀.num_nodes + (max_arg_size bpr₁ bpr₂ x₀ arg₀))

def bdd_size (x₀ : tree unit) (arg₀ : α) : iterator_stack α β → Prop
| (sum.inl (x, arg, res)) := size x ≤ size x₀ ∧
      size arg ≤ max_arg_size bpr₁ bpr₂ x₀ arg₀ ∧ 
      size res ≤ max_res_size bb bpr₁ bpr₂ bpo x₀ arg₀ 
| (sum.inr res) := size res ≤ max_res_size bb bpr₁ bpr₂ bpo x₀ arg₀

variables {bb bpr₁ bpr₂ bpo}

lemma max_res_size_node (l r : tree unit) (arg : α) :
  max_res_size bb bpr₁ bpr₂ bpo (l △ r) arg =
  (l.num_leaves * bb.eval (max_arg_size bpr₁ bpr₂ (l △ r) arg) + l.num_nodes * bpo.eval ((l △ r).num_nodes + (max_arg_size bpr₁ bpr₂ (l △ r) arg))) +
  (r.num_leaves * bb.eval (max_arg_size bpr₁ bpr₂ (l △ r) arg) + r.num_nodes * bpo.eval ((l △ r).num_nodes + (max_arg_size bpr₁ bpr₂ (l △ r) arg))) +
  bpo.eval ((l △ r).num_nodes + (max_arg_size bpr₁ bpr₂ (l △ r) arg)) :=
by { simp [max_res_size], ring, }

lemma max_arg_size_le₁ (hbpr₁ : ∀ x y a, size (pre₁ x y a) ≤ (size a) + bpr₁.eval (size (x △ y))) (l r : tree unit) (arg : α) :
  max_arg_size bpr₁ bpr₂ l (pre₁ l r arg) ≤ max_arg_size bpr₁ bpr₂ (l △ r) arg :=
begin
  simp only [max_arg_size, tree.height, add_comm (max l.height r.height), add_mul, one_mul, ← add_assoc],
  mono*,
  exacts [(hbpr₁ _ _ _).trans le_self_add, le_max_left _ _,
    (l △ r).left_num_nodes_le, (l △ r).left_num_nodes_le, zero_le', zero_le'],
end

lemma max_arg_size_le₂ (hbpr₂ : ∀ x y a, size (pre₂ x y a) ≤ (size a) + bpr₂.eval (size (x △ y))) (l r : tree unit) (arg : α) :
  max_arg_size bpr₁ bpr₂ r (pre₂ l r arg) ≤ max_arg_size bpr₁ bpr₂ (l △ r) arg :=
begin
  simp only [max_arg_size, tree.height, add_comm (max l.height r.height), add_mul, one_mul, ← add_assoc],
  mono*,
  exacts [(hbpr₂ _ _ _).trans (add_le_add_right le_self_add _),
    le_max_right _ _, (l △ r).right_num_nodes_le, (l △ r).right_num_nodes_le, zero_le', zero_le'],
end

lemma max_res_size_le₁ (hbpr₁ : ∀ x y a, size (pre₁ x y a) ≤ (size a) + bpr₁.eval (size (x △ y))) (l r : tree unit) (arg : α) :
  max_res_size bb bpr₁ bpr₂ bpo l (pre₁ l r arg) ≤ max_res_size bb bpr₁ bpr₂ bpo (l △ r) arg :=
let h : max_arg_size bpr₁ bpr₂ l (pre₁ l r arg) ≤ max_arg_size bpr₁ bpr₂ (l △ r) arg := max_arg_size_le₁ hbpr₁ _ _ _ in
(add_le_add (mul_le_mul' le_self_add (bb.eval_mono h)) (mul_le_mul' (l △ r).left_num_nodes_le (bpo.eval_mono $ add_le_add (l △ r).left_num_nodes_le h)))

lemma max_res_size_le₂ (hbpr₂ : ∀ x y a, size (pre₂ x y a) ≤ (size a) + bpr₂.eval (size (x △ y))) (l r : tree unit) (arg : α) :
  max_res_size bb bpr₁ bpr₂ bpo r (pre₂ l r arg) ≤ max_res_size bb bpr₁ bpr₂ bpo (l △ r) arg :=
let h : max_arg_size bpr₁ bpr₂ r (pre₂ l r arg) ≤ max_arg_size bpr₁ bpr₂ (l △ r) arg := max_arg_size_le₂ hbpr₂ _ _ _ in
add_le_add (mul_le_mul' le_add_self (bb.eval_mono h)) (mul_le_mul' (l △ r).right_num_nodes_le (bpo.eval_mono $ add_le_add (l △ r).right_num_nodes_le h))

include hbpr₁ hbpr₂

lemma add_max_res_size_le (l r : tree unit) (arg : α) :
  max_res_size bb bpr₁ bpr₂ bpo l (pre₁ l r arg) + max_res_size bb bpr₁ bpr₂ bpo r (pre₂ l r arg) + bpo.eval (size (l △ r, arg)) ≤
    max_res_size bb bpr₁ bpr₂ bpo (l △ r) arg :=
begin
  have h₁ : max_arg_size bpr₁ bpr₂ l (pre₁ l r arg) ≤ max_arg_size bpr₁ bpr₂ (l △ r) arg := max_arg_size_le₁ hbpr₁ _ _ _,
  have h₂ : max_arg_size bpr₁ bpr₂ r (pre₂ l r arg) ≤ max_arg_size bpr₁ bpr₂ (l △ r) arg := max_arg_size_le₂ hbpr₂ _ _ _,
  conv_rhs { rw max_res_size_node, }, simp only [max_res_size, polysize.prod_size],
  mono*,
  exacts [zero_le', (l △ r).left_num_nodes_le, zero_le', zero_le', (l △ r).right_num_nodes_le, zero_le', le_self_add],
end

include hbb hbpo

theorem stack_step_iter_le (x : tree unit) (arg : α) (n : ℕ)
  (e : iterator_stack α β) (he : e ∈ ((stack_step base pre₁ pre₂ post)^[n] [sum.inl (x, arg, none)])) :
  bdd_size bb bpr₁ bpr₂ bpo x arg e :=
begin
  refine stack_step_induction _ _ _ _ _ _ _ _ _ _ _ he; clear he e x arg n,
  { intros t arg, refine ⟨rfl.le, le_self_add, zero_le'⟩, },
  { intros l r arg res _ h, refine ⟨rfl.le, le_self_add, trans h (max_res_size_le₁ hbpr₁ _ _ _)⟩, },
  { intros arg, refine (hbb _).trans (le_add_right _), simpa using bb.eval_mono le_self_add, },
  { intros l r arg e he, 
    rcases e with (⟨x, arg', res⟩|res),
    { exact ⟨he.1.trans (l △ r).left_num_nodes_le, he.2.1.trans (max_arg_size_le₁ hbpr₁ _ _ _), he.2.2.trans (max_res_size_le₁ hbpr₁ _ _ _)⟩, },
    exact trans he (max_res_size_le₁ hbpr₁ _ _ _), },
  { intros l r arg e he,
    rcases e with (⟨x, arg', res⟩|res),
    { exact ⟨he.1.trans (l △ r).right_num_nodes_le, he.2.1.trans (max_arg_size_le₂ hbpr₂ _ _ _), he.2.2.trans (max_res_size_le₂ hbpr₂ _ _ _)⟩, },
    exact trans he (max_res_size_le₂ hbpr₂ _ _ _), },
  { intros l r arg res₁ res₂ _ _ ih₁ ih₂, 
    rw [bdd_size] at ih₁ ih₂ ⊢,
    refine (hbpo _ _ _ _ _).trans _,
    refine trans _ (add_max_res_size_le hbpr₁ hbpr₂ _ _ _), 
    mono*, },
end

end

section

variables {α β γ : Type} [tencodable α] [tencodable β] [tencodable γ]
  [polysize α] [polysize β] [polysize γ]
  {st : γ → tree unit} {arg : γ → α}
  {base : γ → α → β} {pre₁ pre₂ : γ → tree unit → tree unit → α → α}
  {post : γ → β → β → tree unit → tree unit → α → β}
  (hst : polysize_fun st) (harg : polysize_fun arg)
  (hb : polysize_fun base)
  (hpr₁ : polysize_safe (λ (usf : γ × tree unit × tree unit) (a : α), pre₁ usf.1 usf.2.1 usf.2.2 a))
  (hpr₂ : polysize_safe (λ (usf : γ × tree unit × tree unit) (sf : α), pre₂ usf.1 usf.2.1 usf.2.2 sf))
  (hpo : polysize_safe (λ (usf : γ × tree unit × tree unit × α) (sf : β × β), post usf.1 sf.1 sf.2 usf.2.1 usf.2.2.1 usf.2.2.2))

@[reducible] noncomputable def _root_.polynomial.peval {α : Type*} [semiring α] (p : polynomial α) (x : α) : polynomial α :=
p.comp ((polynomial.C x) + polynomial.X)

noncomputable def max_arg_size_poly : polynomial ℕ :=
harg.poly + hst.poly * ((hpr₁.poly.comp (polynomial.X + hst.poly)) + (hpr₂.poly.comp (polynomial.X + hst.poly)))

noncomputable def max_res_size_poly : polynomial ℕ :=
(hst.poly + 1) * hb.poly.comp (polynomial.X + max_arg_size_poly hst harg hpr₁ hpr₂) +
  hst.poly * hpo.poly.comp (polynomial.X + hst.poly + max_arg_size_poly hst harg hpr₁ hpr₂)

noncomputable def bdd_size_poly : polynomial ℕ :=
hst.poly + (max_arg_size_poly hst harg hpr₁ hpr₂) + (max_res_size_poly hst harg hb hpr₁ hpr₂ hpo)

lemma arg_poly_le (x : γ) :
  max_arg_size (hpr₁.poly.peval (size x)) (hpr₂.poly.peval (size x)) (st x) (arg x) ≤
   (max_arg_size_poly hst harg hpr₁ hpr₂).eval (size x) :=
begin
  have := hst.spec x, have := harg.spec x,
  simp only [max_arg_size_poly, max_arg_size, polynomial.eval_add, polynomial.eval_X,
    polynomial.eval_mul, polysize.prod_size, polysize_tree_unit, polynomial.eval_comp, polynomial.eval_C],
  mono*,
  exacts [(st x).height_le_num_nodes.trans (hst.spec x), zero_le', zero_le'],
end

lemma res_poly_le (x : γ) :
  max_res_size (hb.poly.peval (size x)) (hpr₁.poly.peval (size x)) (hpr₂.poly.peval (size x)) (hpo.poly.peval (size x)) (st x) (arg x) ≤
    (max_res_size_poly hst harg hb hpr₁ hpr₂ hpo).eval (size x) :=
begin
  have := hst.spec, have := arg_poly_le hst harg hpr₁ hpr₂ x,
  simp only [max_res_size, max_res_size_poly, polynomial.peval, ←add_assoc, eq_nat_cast,
    polynomial.eval_comp, polynomial.eval_add, polynomial.eval_nat_cast, nat.cast_id, polynomial.eval_X,
    polynomial.eval_mul, polynomial.eval_one, (st x).num_leaves_eq_num_nodes_succ],
  mono*; exact zero_le',
end

lemma bdd_size_poly_le (x : γ) (e : iterator_stack α β)
  (he : bdd_size (hb.poly.peval (size x)) (hpr₁.poly.peval (size x)) (hpr₂.poly.peval (size x)) 
    (hpo.poly.peval (size x)) (st x) (arg x) e) : size e ≤ (bdd_size_poly hst harg hb hpr₁ hpr₂ hpo).eval (size x) :=
begin
  rcases e with (⟨t, a, res⟩|res),
  { conv_lhs { simp [← add_assoc], },
    simp [bdd_size, bdd_size_poly] at ⊢ he,
    exact add_le_add (add_le_add (he.1.trans $ hst.spec x) 
      (he.2.1.trans $ arg_poly_le _ _ _ _ x))
      (he.2.2.trans $ res_poly_le _ _ _ _ _ _ x), },
  { simp [bdd_size, bdd_size_poly] at he ⊢,
    exact le_add_left (he.trans $ res_poly_le _ _ _ _ _ _ x), }
end

  -- suffices : size e ≤ (bdd_size_poly bb bpr₁ bpr₂ bpo).eval (size (st x, arg x)),
  -- { refine this.trans _, clear_except hbst hbarg, simp, mono*, },

include hst harg hb hpr₁ hpr₂ hpo

theorem stack_step_iter_le' : ∃ (p : polynomial ℕ),
  ∀ (x : γ) (n : ℕ)
  (e : iterator_stack α β) (he : e ∈ ((stack_step (base x) (pre₁ x) (pre₂ x) (post x))^[n] [sum.inl (st x, arg x, none)])),
  size e ≤ p.eval (size x) :=
begin
  use (bdd_size_poly hst harg hb hpr₁ hpr₂ hpo),
  intros x n e he,
  apply bdd_size_poly_le, apply stack_step_iter_le _ _ _ _ _ _ n e he,
  { intro a, simpa using hb.spec (x, a), },
  { intros l r a, refine (hpr₁.spec (x, l, r) a).trans _, simp [add_assoc], mono*, exact nat.le_succ _, },
  { intros l r a, refine (hpr₂.spec (x, l, r) a).trans _, simp [add_assoc], mono*, exact nat.le_succ _, },
  { intros ih₁ ih₂ l r a, refine (hpo.spec (x, l, r, a) (ih₁, ih₂)).trans _, simp [add_assoc], mono*, exact le_add_self, }
end

theorem stack_step_polysize : ∃ (p : polynomial ℕ), ∀ (x : γ) (n : ℕ),
  size ((stack_step (base x) (pre₁ x) (pre₂ x) (post x))^[n] [sum.inl (st x, arg x, none)]) ≤
    p.eval (size x) :=
begin
  cases stack_step_iter_le' hst harg hb hpr₁ hpr₂ hpo with p hp,
  use (5 * hst.poly + 2) * (p + 1),
  intros x n,
  simp only [polynomial.eval_add, polynomial.eval_mul, polynomial.eval_one],
  apply list.size_le_mul_of_le,
  { refine (stack_step_iter_len_le' _ _ _).trans _, simpa [tree.time_steps, add_assoc] using hst.spec x, },
  { exact hp x n, },
end

end

end tree


/-
# Theorem:

Suppose
  - `|base(a)| ≤ P₁(|a|)`,
  - `|pre₁(left, right, a)| ≤ |a| + P₂(|left|, |right|)`
  - `idem for pre₂, say with P₂'`
  - `|post(ih₁, ih₂, left, right, a) ≤ |ih₁| + |ih₂| + P₃(|left|, |right|, |a|)`
Then, if we iterate `stack_step` starting with `(x, arg, none) :: xs`, the
size of any intermediate state (≤ x.time_steps steps later)
is bounded by `|xs| + F(x, |arg|)` (assume `F` is mono)

We should have `F(x, |arg|) ≈ `:
    max arg that can appear: `x.depth * (P₂(x) + P₂'(x))`
    `P₁(x.depth * (P₂(x) + P₂'(x)))` <-- max base value
    `P₁(x.depth * (P₂(x) + P₂'(x))) + t.num_nodes * P₃(x, x.depth * (P₂(x) + P₂'(x)))`
      <-- max result value at node `t`
    - `P₁(x.depth * (P₂(x) + P₂'(x))) + x.num_nodes * P₃(x, x.depth * (P₂(x) + P₂'(x)))`


Proof:
Suppose it is true when we start with `(x, arg, none)` and `(y, arg, none)`
Then suppose we start with `(x △ y, arg, none)`

Immediately, the next step is to append `(x, pre₁ x y arg, none)` to the stack.
After in the next `x.time_steps` steps, the `x`-portion of the stack is bounded
by `F(|x|, |pre₁ x y arg|) ≤ F(|x|, |arg| + P₂(|x|, |y|)`
Then, we end up with `(result: r₁) :: (x △ y, arg, none)` with `r₁ ≤ F(|x|, |arg| + P₂(|x|, |y|))`

Then we turn this into `(x △ y, arg, r₁)` which expands back into
`(y, pre₂ x y arg, none)`. Everything here is bounded by
`F(|y|, |arg| + P₂'(|x|, |y|))` and we end up with
`(result : r₂) :: (x △ y, arg, r₂)`, where `r₂ ≤ F(|y|, |arg| + P₂'(|x|, |y|))`

When we combine these, in total, we get 
`result = post r₁ r₂ x y arg`
so that `|result| ≤ |r₁| + |r₂| + P₃(|x|, |y|, |arg|) ≤ F(|x|, |arg| + P₂(|x|, |y|)) + F(|y|, |arg| + P₂'(|x|, |y|)) + P₃(|x|, |y|, |arg|)`

Thus, the recursive equation needed is

F(|x △ y|, |arg|) ≥ F(|x|, |arg| + P₂(|x|, |y|) +
  F(|y|, |arg| + P₂'(|x|, |y|) +
  P₃(|x|, |y|, |arg|)



-/
-- 

