import data.list.big_operators
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

lemma list.encode_num_nodes_eq : ∀ (x : list α),
  (encode x).num_nodes = x.length + (x.map $ λ e, (encode e).num_nodes).sum
| [] := rfl
| (hd :: tl) := by { simp [encode_cons, tl.encode_num_nodes_eq], abel, }

lemma list.len_le_encode (x : list α) : x.length ≤ (encode x).num_nodes :=
by { rw x.encode_num_nodes_eq, exact le_self_add, }

lemma list.encode_le_encode_of_mem {x : list α} {y : α} (h : y ∈ x) :
  (encode y).num_nodes < (encode x).num_nodes :=
begin
  rw [x.encode_num_nodes_eq, ← multiset.coe_sum],
  refine lt_add_of_pos_of_le (list.length_pos_of_mem h) (multiset.le_sum_of_mem _),
  simp, exact ⟨_, h, rfl⟩,
end

@[simp] lemma encode_sum_inl_num_nodes (x : α) :
  (encode (sum.inl x : α ⊕ β)).num_nodes = (encode x).num_nodes + 1 := by simp [encode]

@[simp] lemma encode_sum_inr_num_nodes (x : β) :
  (encode (sum.inr x : α ⊕ β)).num_nodes = (encode x).num_nodes + 2 :=
by { simp [encode], ring, }

variables [polysize α] [polysize β] [polysize γ]

instance : polysize (α × β) :=
{ size := λ x : α × β, size x.1 + size x.2,
  upper := begin
    cases upper α with p hp, cases upper β with q hq,
    use p + q, rintro ⟨x₁, x₂⟩,
    rw polynomial.eval_add,
    refine add_le_add ((hp _).trans $ p.eval_mono _) ((hq _).trans $ q.eval_mono _);
    simp [encode]; linarith only,
  end,
  lower := begin
    cases lower α with p hp, cases lower β with q hq,
    use p + q + 1, rintro ⟨x₁, x₂⟩,
    simp only [encode, num_nodes, polynomial.eval_add, polynomial.eval_one, add_le_add_iff_right],
    exact add_le_add ((hp _).trans $ p.eval_mono le_self_add)
      ((hq _).trans $ q.eval_mono le_add_self),
  end }

instance : polysize (option α) :=
{ size := λ x, x.elim 0 size,
  upper := begin
    cases upper α with p hp, use p,
    rintro (_|x), { simp, },
    simp only [encode, option.elim, num_nodes, zero_add],
    refine (hp _).trans (p.eval_mono _), simp,
  end,
  lower := begin
    cases lower α with p hp, use p + 1,
    rintro (_|x), { simp [encode], },
    simpa [encode] using hp _,
  end }

@[simp] lemma polysize.prod_size (x : α) (y : β) : size (x, y) = size x + size y := rfl

instance : polysize (list α) :=
{ size := λ l, l.length + (l.map size).sum,
  upper := begin
    cases upper α with p hp,
    use polynomial.X + polynomial.X * p,
    intro x, simp,
    refine add_le_add x.len_le_encode ((list.sum_le_card_nsmul _ (p.eval (encode x).num_nodes) _).trans _),
    { simpa using λ a ha, (hp a).trans (p.eval_mono (list.encode_le_encode_of_mem ha).le), },
    simpa using nat.mul_le_mul_right _ x.len_le_encode,
  end,
  lower := begin
    cases lower α with p hp,
    use polynomial.X + polynomial.X * p,
    intro x, simp [x.encode_num_nodes_eq, add_assoc],
    refine le_add_left ((list.sum_le_card_nsmul _ (p.eval (x.map size).sum) _).trans _),
    { simp, intros a ha, refine (hp _).trans (p.eval_mono _), 
      rw ← multiset.coe_sum, apply multiset.le_sum_of_mem,
      simp, exact ⟨_, ha, rfl⟩, },
    simpa using nat.mul_le_mul le_self_add (p.eval_mono le_add_self),
  end }

@[simp] lemma size_nil : size ([] : list α) = 0 := rfl
@[simp] lemma size_cons (x : α) (xs : list α) : size (x :: xs) = size x + size xs + 1 :=
by { simp [size], abel, }

lemma list.size_le_mul_of_le (a b : ℕ) (l : list α)
  (h₁ : l.length ≤ a) (h₂ : ∀ x ∈ l, size x ≤ b) :
  size l ≤ a * (b + 1) :=
begin
  simp only [size, add_comm b 1, mul_add, mul_one],
  refine add_le_add h₁ ((list.sum_le_card_nsmul _ b _).trans _),
  { simpa using h₂, }, { simpa using mul_le_mul_right' h₁ b, }
end

instance : polysize (α ⊕ β) :=
{ size := λ x, x.elim size size,
  upper := begin
    cases upper α with p hp, cases upper β with q hq,
    use p + q,
    rintros (x|x); simp,
    exacts [le_add_right ((hp x).trans (p.eval_mono le_self_add)),
            le_add_left ((hq x).trans (q.eval_mono le_self_add))],
  end,
  lower := begin
    cases lower α with p hp, cases lower β with q hq,
    use p + q + 2,
    rintros (x|x); simp,
    exacts [add_le_add (le_add_right (hp x)) one_le_two,
            le_add_left (hq x)],
  end }

@[simp] lemma size_inl (x : α) : size (sum.inl x : α ⊕ β) = size x := rfl
@[simp] lemma size_inr (x : β) : size (sum.inr x : α ⊕ β) = size x := rfl

instance : polysize ℕ := default
instance : polysize (tree unit) := default

@[simp] lemma polysize_unary_nat (n : ℕ) : size n = n :=
by simp [polysize.size]

@[simp] lemma polysize_tree_unit (x : tree unit) : size x = x.num_nodes := rfl

def polysize_safe (f : α → β → γ) : Prop :=
∃ (p : polynomial ℕ), ∀ x y, size (f x y) ≤ size y + p.eval (size x)

theorem polysize_safe.iterate {f : α → β → β} {n : α → ℕ}
  (hf : polysize_safe f) (hn : ∃ p : polynomial ℕ, ∀ x, n x ≤ p.eval (size x)) :
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
