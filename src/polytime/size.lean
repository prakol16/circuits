import encode

open tencodable function tree
variables {α β γ : Type*}

class polysize (α : Type*) [tencodable α] :=
(size : α → ℕ)
(upper [] : ∃ p : polynomial ℕ, ∀ x, size x ≤ p.eval (encode x).num_nodes)
(lower [] : ∃ p : polynomial ℕ, ∀ x, (encode x).num_nodes ≤ p.eval (size x))

open polysize
variables [tencodable α] [tencodable β] [tencodable γ]

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
    ∃ p : mv_polynomial (fin 2) ℕ, ∀ x y (m ≤ n x), size ((f x)^[m] y) ≤ mv_polynomial.eval ![size x, size y] p :=
begin
  cases hn with p hn, cases hf with q hf,
  use (mv_polynomial.X 1 + (polynomial.to_mv 0 p) * (polynomial.to_mv 0 q) : mv_polynomial (fin 2) ℕ),
  intros x y m hm, specialize hn x,
  have : ∀ n : ℕ, size ((f x)^[n] y) ≤ size y + n * (q.eval $ size x),
  { intro n, induction n with n ih, 
    { simp, },
    rw [iterate_succ_apply', nat.succ_mul, ← add_assoc],
    refine (hf x _).trans _,
    simpa using ih, },
  refine (this $ m).trans _,
  simp, mono, exacts [hm.trans hn, zero_le'],
end

def polysize_uniform' {β : α → Type*} [∀ x, tencodable (β x)] [polysize α] [∀ x, polysize (β x)] [polysize γ]
  (f : ∀ x, β x → γ) : Prop :=
∃ (p : polynomial ℕ), ∀ x y, size (f x y) ≤ size y + p.eval (size x)

theorem polysize_uniform'.iterate [polysize α] [polysize β] {f : α → β → β} {n : α → ℕ}
  (hf : polysize_uniform' f) (hn : ∃ p : polynomial ℕ, ∀ x, n x ≤ p.eval (size x)) :
    ∃ p : mv_polynomial (fin 2) ℕ, ∀ x y (m ≤ n x), size ((f x)^[m] y) ≤ mv_polynomial.eval ![size x, size y] p :=
begin
  cases hn with p hn, cases hf with q hf,
  use (mv_polynomial.X 1 + (polynomial.to_mv 0 p) * (polynomial.to_mv 0 q) : mv_polynomial (fin 2) ℕ),
  intros x y m hm, specialize hn x,
  have : ∀ n : ℕ, size ((f x)^[n] y) ≤ size y + n * (q.eval $ size x),
  { intro n, induction n with n ih, 
    { simp, },
    rw [iterate_succ_apply', nat.succ_mul, ← add_assoc],
    refine (hf x _).trans _,
    simpa using ih, },
  refine (this $ m).trans _,
  simp, mono, exacts [hm.trans hn, zero_le'],
end
