import data.list.basic
import data.polynomial.eval
import data.mv_polynomial.basic
import tree

namespace list

section all_some

@[simp] lemma all_some_nil {α : Type*} : (@list.nil $ option α).all_some = some [] := rfl

@[simp] lemma all_some_cons_none {α} (x : list (option α)) :
  (none :: x).all_some = none := rfl

@[simp] lemma all_some_cons_some {α} (x : list (option α)) (y) :
  (some y :: x).all_some = x.all_some.map (list.cons y) := rfl

@[simp] theorem all_some_of_map_some {α} (x : list α) :
  (x.map some).all_some = some x :=
by induction x; simp [*]

end all_some

end list

namespace tree

lemma left_num_nodes_le {α} : ∀ (x : tree α), x.left.num_nodes ≤ x.num_nodes
| nil := rfl.le
| (node _ a b) := nat.le_succ_of_le le_self_add

lemma right_num_nodes_le {α} : ∀ (x : tree α), x.right.num_nodes ≤ x.num_nodes
| nil := rfl.le
| (node _ a b) := nat.le_succ_of_le le_add_self

end tree

namespace polynomial

@[mono]
lemma eval_mono (p : polynomial ℕ) : monotone (λ n : ℕ, p.eval n) :=
begin
  induction p using polynomial.induction_on' with p q h₀ h₁ n a,
  { simp, apply monotone.add; assumption, },
  simp, apply monotone.const_mul _ (zero_le a),
  { intros x y hxy, apply pow_le_pow_of_le_left (zero_le x) hxy, }, 
end

noncomputable def to_mv {R σ : Type*} [comm_semiring R] (x : σ) :
  polynomial R →+* mv_polynomial σ R := polynomial.eval₂_ring_hom mv_polynomial.C (mv_polynomial.X x)

@[simp] lemma to_mv_eval {R σ : Type*} [comm_semiring R] {x : σ} (p : polynomial R) (i : σ → R) :
  mv_polynomial.eval i (to_mv x p) = p.eval (i x) :=
by { rw [← coe_eval_ring_hom, to_mv, ← ring_hom.comp_apply], congr, ext; simp, }

end polynomial

namespace mv_polynomial
variables {σ : Type*} {R : Type*} [comm_semiring R]

noncomputable def to_polynomial (p : mv_polynomial σ R) : polynomial R :=
p.eval₂ polynomial.C (λ _, polynomial.X)

lemma to_polynomial_eval_eq_coe (p : mv_polynomial σ R) (x : R) :
  p.to_polynomial.eval x = (polynomial.eval_ring_hom x).comp (mv_polynomial.eval₂_hom (@polynomial.C R _) (λ _, polynomial.X)) p :=
rfl

@[simp] lemma to_polynomial_eval_diag (p : mv_polynomial σ R) (x : R) :
  mv_polynomial.eval (λ _ : σ, x) p = p.to_polynomial.eval x :=
begin
  rw to_polynomial_eval_eq_coe,
  apply mv_polynomial.hom_eq_hom,
  { ext y, simp, },
  { intro n, simp, },
end

lemma eval_mono (p : mv_polynomial σ ℕ) : monotone (λ x : σ → ℕ, mv_polynomial.eval x p) :=
begin
  induction p using mv_polynomial.induction_on with n p q ih₁ ih₂ p x ih,
  { simpa using monotone_const, },
  { simp, apply monotone.add; assumption, },
  simp, apply monotone.mul,
  exacts [ih, function.monotone_eval _, λ _, zero_le', λ _, zero_le'],
end

lemma le_to_polynomial_of_le (p : mv_polynomial σ ℕ) (a : ℕ) (x : σ → ℕ)
  (hx : ∀ i, x i ≤ a) : mv_polynomial.eval x p ≤ p.to_polynomial.eval a :=
calc mv_polynomial.eval x p ≤ mv_polynomial.eval (λ _, a) p : p.eval_mono hx
                      ...   = p.to_polynomial.eval a : p.to_polynomial_eval_diag a

lemma le_to_polynomial_of_le_sum₂ (p : mv_polynomial (fin 2) ℕ) (x y : ℕ) :
  mv_polynomial.eval ![x, y] p ≤ p.to_polynomial.eval (x + y) :=
by { apply le_to_polynomial_of_le, simp [fin.forall_fin_two], }

lemma to_polynomial_le_of_le (p : mv_polynomial σ ℕ) (a : ℕ) (x : σ → ℕ)
  (hx : ∀ i, a ≤ x i) : p.to_polynomial.eval a ≤ mv_polynomial.eval x p :=
calc p.to_polynomial.eval a = mv_polynomial.eval (λ _, a) p : (p.to_polynomial_eval_diag a).symm
                        ... ≤ mv_polynomial.eval x p : p.eval_mono hx

end mv_polynomial

namespace list

theorem scanl_nth_le_eq_foldl {α β : Type*} (l : list β) (f : α → β → α) (x : α)
  (n : ℕ) (hn : n < (l.scanl f x).length) :
  (l.scanl f x).nth_le n hn = (l.take n).foldl f x :=
begin
  revert hn, simp only [length_scanl],
  induction l with hd tl ih generalizing x n, { simp, },
  cases n, { simp, }, 
  simpa [nat.succ_eq_add_one] using ih (f x hd) n,
end

theorem scanl_last_eq_foldl {α β : Type*} (l : list β) (f : α → β → α) (x : α) :
  (l.scanl f x).last' = some (l.foldl f x) :=
by simp [last'_eq_last_of_ne_nil (ne_nil_of_length_eq_succ (l.length_scanl x)), last_eq_nth_le, l.scanl_nth_le_eq_foldl f x, l.length_scanl x]

@[simp] theorem reverse_last' {α : Type*} (l : list α) :
  l.reverse.last' = l.head' := by cases l; simp

@[simp] theorem reverse_head' {α : Type*} (l : list α) :
  l.reverse.head' = l.last' := by simpa [eq_comm] using l.reverse.reverse_last'

end list
