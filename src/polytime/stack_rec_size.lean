import polytime.size
import stack_rec

open tree function polysize (size)
open_locale tree

variables {α : Type} {β : Type} [tencodable α] [tencodable β]
  [polysize α] [polysize β]
  (base : α → β) (pre₁ pre₂ : tree unit → tree unit → α → α)
  (post : β → β → tree unit → tree unit → α → β)

namespace tree

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
  -- In the inductive step, we first show that `P` is true of the previous results (used several times later)
  have P_l_res : P l (pre₁ l r arg) (sum.inr $ stack_rec base pre₁ pre₂ post l (pre₁ l r arg)),
  { refine (ih₁ _ [] _ _ rfl.le _).resolve_right not_false, simp, },
  have P_r_res : P r (pre₂ l r arg) (sum.inr $ stack_rec base pre₁ pre₂ post r (pre₂ l r arg)),
  { refine (ih₂ _ [] _ _ rfl.le _).resolve_right not_false, simp, },
  -- Now we consider intermediate stages `1 ≤ n ≤ l.time_steps`
  by_cases H : n ≤ l.time_steps,
  { clear ih₂, rcases ih₁ (pre₁ l r arg) _ n e H he with (ih|rfl|ih),
    { left, exact hi₁ ih, }, { left, exact hb _ _, }, { right, exact ih, } },
  -- Now we consider the cases `n = l.time_steps + 1` and `n = l.time_steps + 2`
  rcases lt_iff_exists_add.mp (lt_of_not_le H) with ⟨c, hc, rfl⟩, clear H,
  rw [iterate_succ_apply, add_comm l.time_steps, iterate_add_apply, stack_step, stack_step_iterate] at he,
  cases c, { cases not_lt_zero' hc, }, clear hc,
  cases c, { refine or.imp_left _ he, rintro rfl, exact hb' rfl P_l_res, },
  by_cases H : c ≤ r.time_steps,
  { rcases ih₂ (pre₂ l r arg) _ c e H he with (ih|rfl|ih),
    { left, exact hi₂ ih, }, { left, exact hb' rfl P_l_res, }, { right, exact ih, }, },
  obtain rfl : c = 1 + r.time_steps,
  { simp [time_steps_node, nat.succ_eq_add_one] at hn, 
    linarith only [H, hn], },
  simp [iterate_add] at he,
  refine he.imp_left _, rintro rfl,
  exact hp rfl rfl P_l_res P_r_res,
end

section
variables  (bb bpr₁ bpr₂ bpo : polynomial ℕ)
  (hbb : ∀ x, size (base x) ≤ bb.eval (size x))
  (hbpr₁ : ∀ x y a, size (pre₁ x y a) ≤ (size a) + bpr₁.eval (size (x △ y)))
  (hbpr₂ : ∀ x y a, size (pre₂ x y a) ≤ (size a) + bpr₂.eval (size (x △ y)))
  (hbpo : ∀ ih₁ ih₂ x y a, size (post ih₁ ih₂ x y a) ≤ (size ih₁) + (size ih₂) + bpo.eval (size (x △ y, a)))

def max_arg_size (x₀ : tree unit) (arg₀ : α) : ℕ :=
size arg₀ + x₀.height * ((bpr₁.eval x₀.num_nodes) + (bpr₂.eval x₀.num_nodes))

def max_res_size (x₀ : tree unit) (arg₀ : α) : ℕ :=
x₀.num_leaves * bb.eval (max_arg_size bpr₁ bpr₂ x₀ arg₀) + x₀.num_nodes * bpo.eval (x₀.num_nodes + (max_arg_size bpr₁ bpr₂ x₀ arg₀))

lemma max_res_size_node (l r : tree unit) (arg : α) :
  max_res_size bb bpr₁ bpr₂ bpo (l △ r) arg =
  (l.num_leaves * bb.eval (max_arg_size bpr₁ bpr₂ (l △ r) arg) + l.num_nodes * bpo.eval ((l △ r).num_nodes + (max_arg_size bpr₁ bpr₂ (l △ r) arg))) +
  (r.num_leaves * bb.eval (max_arg_size bpr₁ bpr₂ (l △ r) arg) + r.num_nodes * bpo.eval ((l △ r).num_nodes + (max_arg_size bpr₁ bpr₂ (l △ r) arg))) +
  bpo.eval ((l △ r).num_nodes + (max_arg_size bpr₁ bpr₂ (l △ r) arg)) :=
by { simp [max_res_size], ring, }


def bdd_size (x₀ : tree unit) (arg₀ : α) : iterator_stack α β → Prop
| (sum.inl (x, arg, res)) := size x ≤ size x₀ ∧
      size arg ≤ max_arg_size bpr₁ bpr₂ x₀ arg₀ ∧ 
      size res ≤ max_res_size bb bpr₁ bpr₂ bpo x₀ arg₀ 
| (sum.inr res) := size res ≤ max_res_size bb bpr₁ bpr₂ bpo x₀ arg₀

noncomputable def max_arg_size_poly : polynomial ℕ :=
polynomial.X + polynomial.X * (bpr₁ + bpr₂)

lemma arg_poly_le (x₀ : tree unit) (arg₀ : α) :
  max_arg_size bpr₁ bpr₂ x₀ arg₀ ≤  (max_arg_size_poly bpr₁ bpr₂).eval (size (x₀, arg₀)) :=
begin
  simp only [max_arg_size_poly, max_arg_size, polynomial.eval_add, polynomial.eval_X, polynomial.eval_mul, polysize.prod_size, polysize_tree_unit],
  mono*,
  exacts [le_add_self, x₀.height_le_num_nodes.trans le_self_add, le_self_add, le_self_add, zero_le', zero_le'],
end

noncomputable def max_res_size_poly : polynomial ℕ :=
(polynomial.X + 1) * (bb.comp (max_arg_size_poly bpr₁ bpr₂)) +
  polynomial.X * (bpo.comp (polynomial.X + max_arg_size_poly bpr₁ bpr₂))

lemma res_poly_le (x₀ : tree unit) (arg₀ : α) :
  max_res_size bb bpr₁ bpr₂ bpo x₀ arg₀ ≤ (max_res_size_poly bb bpr₁ bpr₂ bpo).eval (size (x₀, arg₀)) :=
begin
  have := arg_poly_le bpr₁ bpr₂ x₀ arg₀,
  simp only [max_res_size_poly, max_res_size, x₀.num_leaves_eq_num_nodes_succ, polysize.prod_size, polysize_tree_unit,
    polynomial.eval_add, polynomial.eval_mul, polynomial.eval_X, polynomial.eval_one, polynomial.eval_comp],
  mono*,
  exacts [le_self_add, zero_le', zero_le', le_self_add, le_self_add, zero_le', zero_le'],
end

noncomputable def bdd_size_poly : polynomial ℕ :=
polynomial.X + (max_arg_size_poly bpr₁ bpr₂) + (max_res_size_poly bb bpr₁ bpr₂ bpo)

lemma bdd_size_poly_le (x₀ : tree unit) (arg₀ : α) (e : iterator_stack α β)
  (he : bdd_size bb bpr₁ bpr₂ bpo x₀ arg₀ e) : size e ≤ (bdd_size_poly bb bpr₁ bpr₂ bpo).eval (size (x₀, arg₀)) :=
begin
  rcases e with (⟨x, arg, res⟩|res),
  { conv_lhs { simp [← add_assoc], },
    simp [bdd_size, bdd_size_poly, -polysize.prod_size] at he ⊢,
    exact add_le_add (add_le_add (he.1.trans le_self_add) (he.2.1.trans $ arg_poly_le _ _ _ _)) (he.2.2.trans $ res_poly_le _ _ _ _ _ _), },
  { simp [bdd_size, bdd_size_poly] at he ⊢, 
    refine le_add_left (he.trans $ res_poly_le _ _ _ _ _ _), }
end

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
let h : max_arg_size bpr₁ bpr₂ l (pre₁ l r arg) ≤ max_arg_size bpr₁ bpr₂ (l △ r) arg := max_arg_size_le₁ _ _ _ hbpr₁ _ _ _ in
(add_le_add (mul_le_mul' le_self_add (bb.eval_mono h)) (mul_le_mul' (l △ r).left_num_nodes_le (bpo.eval_mono $ add_le_add (l △ r).left_num_nodes_le h)))

lemma max_res_size_le₂ (hbpr₂ : ∀ x y a, size (pre₂ x y a) ≤ (size a) + bpr₂.eval (size (x △ y))) (l r : tree unit) (arg : α) :
  max_res_size bb bpr₁ bpr₂ bpo r (pre₂ l r arg) ≤ max_res_size bb bpr₁ bpr₂ bpo (l △ r) arg :=
let h : max_arg_size bpr₁ bpr₂ r (pre₂ l r arg) ≤ max_arg_size bpr₁ bpr₂ (l △ r) arg := max_arg_size_le₂ _ _ _ hbpr₂ _ _ _ in
add_le_add (mul_le_mul' le_add_self (bb.eval_mono h)) (mul_le_mul' (l △ r).right_num_nodes_le (bpo.eval_mono $ add_le_add (l △ r).right_num_nodes_le h))

include hbpr₁ hbpr₂

lemma add_max_res_size_le (l r : tree unit) (arg : α) :
  max_res_size bb bpr₁ bpr₂ bpo l (pre₁ l r arg) + max_res_size bb bpr₁ bpr₂ bpo r (pre₂ l r arg) + bpo.eval (size (l △ r, arg)) ≤
    max_res_size bb bpr₁ bpr₂ bpo (l △ r) arg :=
begin
  have h₁ : max_arg_size bpr₁ bpr₂ l (pre₁ l r arg) ≤ max_arg_size bpr₁ bpr₂ (l △ r) arg := max_arg_size_le₁ _ _ _ hbpr₁ _ _ _,
  have h₂ : max_arg_size bpr₁ bpr₂ r (pre₂ l r arg) ≤ max_arg_size bpr₁ bpr₂ (l △ r) arg := max_arg_size_le₂ _ _ _ hbpr₂ _ _ _,
  conv_rhs { rw max_res_size_node, }, simp only [max_res_size, polysize.prod_size],
  mono*,
  exacts [zero_le', (l △ r).left_num_nodes_le, zero_le', zero_le', (l △ r).right_num_nodes_le, zero_le', le_self_add],
end

include hbb hbpo

theorem stack_step_iter_le (x : tree unit) (arg : α) (n : ℕ)
  (e : iterator_stack α β) (he : e ∈ ((stack_step base pre₁ pre₂ post)^[n] [sum.inl (x, arg, none)])) :
  bdd_size bb bpr₁ bpr₂ bpo x arg e :=
begin
  refine stack_step_induction _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ he; clear he e x arg n,
  { intros t arg, refine ⟨rfl.le, le_self_add, zero_le'⟩, },
  { intros l r arg res _ h, refine ⟨rfl.le, le_self_add, trans h (max_res_size_le₁ _ _ _ _ _ hbpr₁ _ _ _)⟩, },
  { intros arg, refine (hbb _).trans (le_add_right _), simpa using bb.eval_mono le_self_add, },
  { intros l r arg e he, 
    rcases e with (⟨x, arg', res⟩|res),
    { exact ⟨he.1.trans (l △ r).left_num_nodes_le, he.2.1.trans (max_arg_size_le₁ _ _ _ hbpr₁ _ _ _), he.2.2.trans (max_res_size_le₁ _ _ _ _ _ hbpr₁ _ _ _)⟩, },
    exact trans he (max_res_size_le₁ _ _ _ _ _ hbpr₁ _ _ _), },
  { intros l r arg e he,
    rcases e with (⟨x, arg', res⟩|res),
    { exact ⟨he.1.trans (l △ r).right_num_nodes_le, he.2.1.trans (max_arg_size_le₂ _ _ _ hbpr₂ _ _ _), he.2.2.trans (max_res_size_le₂ _ _ _ _ _ hbpr₂ _ _ _)⟩, },
    exact trans he (max_res_size_le₂ _ _ _ _ _ hbpr₂ _ _ _), },
  { intros l r arg res₁ res₂ _ _ ih₁ ih₂, 
    rw [bdd_size] at ih₁ ih₂ ⊢,
    refine (hbpo _ _ _ _ _).trans _,
    refine trans _ (add_max_res_size_le pre₁ pre₂ _ _ _ _ hbpr₁ hbpr₂ _ _ _), 
    mono*, },
end

end

section

variables {base pre₁ pre₂ post}
 (hb : ∃ bb : polynomial ℕ, ∀ x, size (base x) ≤ bb.eval (size x))
 (hpr₁ : polysize_safe (λ (xy : tree unit × tree unit) (a : α), pre₁ xy.1 xy.2 a))
 (hpr₂ : polysize_safe (λ (xy : tree unit × tree unit) (a : α), pre₂ xy.1 xy.2 a))
 (hpo : polysize_safe (λ (xy : tree unit × tree unit × α) (ih : β × β), post ih.1 ih.2 xy.1 xy.2.1 xy.2.2))

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

include hb hpr₁ hpr₂ hpo

theorem stack_step_iter_le' : ∃ (p : polynomial ℕ),
  ∀ (x : tree unit) (arg : α) (n : ℕ)
  (e : iterator_stack α β) (he : e ∈ ((stack_step base pre₁ pre₂ post)^[n] [sum.inl (x, arg, none)])),
  size e ≤ p.eval (size (x, arg)) :=
begin
  cases hb with bb hb, cases hpr₁ with bpr₁ hbpr₁, cases hpr₂ with bpr₂ hbpr₂, cases hpo with bpo hbpo,
  use bdd_size_poly bb bpr₁ bpr₂ bpo,
  intros x arg n e he,
  refine bdd_size_poly_le _ _ _ _ _ _ _ (stack_step_iter_le _ _ _ _ _ _ _ _ _ _ _ _ x arg n e he),
  { exact hb, },
  { intros x y a, exact (hbpr₁ (x, y) a).trans (add_le_add_left (bpr₁.eval_mono $ nat.le_succ (size x + size y)) _), },
  { intros x y a, exact (hbpr₂ (x, y) a).trans (add_le_add_left (bpr₂.eval_mono $ nat.le_succ (size x + size y)) _), },
  { intros ih₁ ih₂ x y a, refine (hbpo (x, y, a) (ih₁, ih₂)).trans _, simp [add_assoc], mono*, exact le_add_self, },
end

theorem stack_step_polysize : ∃ (p : polynomial ℕ), ∀ (x : tree unit) (arg : α) (n : ℕ),
  size ((stack_step base pre₁ pre₂ post)^[n] [sum.inl (x, arg, none)]) ≤
    p.eval (size (x, arg)) :=
begin
  cases stack_step_iter_le' hb hpr₁ hpr₂ hpo with p hp,
  use (5 * polynomial.X + 2) * (p + 1),
  intros x arg n,
  simp only [polynomial.eval_add, polynomial.eval_mul, polynomial.eval_one],
  apply list.size_le_mul_of_le,
  { refine (stack_step_iter_len_le' _ _ _).trans _, simp [tree.time_steps], linarith only, },
  { exact hp x arg n, },
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

