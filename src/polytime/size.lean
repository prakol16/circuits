import data.list.big_operators
import tactic.expand_exists
import complexity_class.tactic
import encode

open tencodable function tree
variables {α β γ δ ε : Type*}

class polysize (α : Type*) [tencodable α] :=
(size : α → ℕ)
(upper [] : ∃ p : polynomial ℕ, ∀ x, size x ≤ p.eval (encode x).num_nodes)
(lower [] : ∃ p : polynomial ℕ, ∀ x, (encode x).num_nodes ≤ p.eval (size x))

open polysize
variables [tencodable α] [tencodable β] [tencodable γ] [tencodable δ] [tencodable ε]

@[instance, priority 10]
def default_polysize : polysize α :=
{ size := λ x, (encode x).num_nodes,
  upper := ⟨polynomial.X, by simp⟩,
  lower := ⟨polynomial.X, by simp⟩ }

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

lemma list.encode_lt_encode_of_mem {x : list α} {y : α} (h : y ∈ x) :
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

variables [polysize α] [polysize β] [polysize γ] [polysize δ] [polysize ε]

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

@[simp] lemma polysize.none_size : size (@none α) = 0 := rfl
@[simp] lemma polysize.some_size (x : α) : size (some x) = size x := rfl
@[simp] lemma polysize.prod_size (x : α) (y : β) : size (x, y) = size x + size y := rfl

instance : polysize (list α) :=
{ size := λ l, l.length + (l.map size).sum,
  upper := begin
    cases upper α with p hp,
    use polynomial.X + polynomial.X * p,
    intro x, simp,
    refine add_le_add x.len_le_encode ((list.sum_le_card_nsmul _ (p.eval (encode x).num_nodes) _).trans _),
    { simpa using λ a ha, (hp a).trans (p.eval_mono (list.encode_lt_encode_of_mem ha).le), },
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

/-- The same as `list.encode_lt_encode_of_mem` but for `size` -/
lemma list.size_lt_of_mem {x : list α} {e : α} (h : e ∈ x) :
  size e < size x :=
begin
  dsimp only [polysize.size],
  rw [← multiset.coe_sum],
  refine lt_add_of_pos_of_le (list.length_pos_of_mem h) (multiset.le_sum_of_mem _),
  simp, exact ⟨_, h, rfl⟩,
end

lemma list.size_le_of_sublist {x y : list α} (h : y <+ x) :
  size y ≤ size x :=
add_le_add h.length_le ((h.map size).sum_le_sum $ λ _ _, zero_le')

lemma list.length_le_size (l : list α) : l.length ≤ size l := le_self_add

@[simp] lemma size_nil : size ([] : list α) = 0 := rfl

@[simp] lemma size_cons (x : α) (xs : list α) : size (x :: xs) = size x + size xs + 1 :=
by { simp [size], abel, }

@[simp] lemma size_append (x y : list α) : size (x ++ y) = size x + size y :=
by { simp [size], abel, }

@[simp] lemma size_reverse (x : list α) : size x.reverse = size x :=
by simp [size, list.sum_reverse]


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

-- Equal to `default_polysize` but more useful defeq
instance : polysize ℕ :=
{ size := λ n, n,
  upper := ⟨polynomial.X, by simp⟩,
  lower := ⟨polynomial.X, by simp⟩ }

instance : polysize (tree unit) := default_polysize

@[simp] lemma polysize_unary_nat (n : ℕ) : size n = n := rfl

@[simp] lemma polysize_tree_unit (x : tree unit) : size x = x.num_nodes := rfl

def polysize_fun {γ : Type*} [has_uncurry γ α β] (f : γ) : Prop :=
∃ (p : polynomial ℕ), ∀ x : α, size (↿f x) ≤ p.eval (size x)

def polysize_safe (f : α → β → γ) : Prop :=
∃ (p : polynomial ℕ), ∀ x y, size (f x y) ≤ size y + p.eval (size x)

@[expand_exists polysize_fun.poly polysize_fun.spec]
lemma polysize_fun.def {γ : Type} [has_uncurry γ α β] {f : γ} (hf : polysize_fun f) :
  ∃ (p : polynomial ℕ), ∀ x : α, size (↿f x) ≤ p.eval (size x) := hf

@[expand_exists polysize_safe.poly polysize_safe.spec]
lemma polysize_safe.def {f : α → β → γ} (hf : polysize_safe f) :
  ∃ (p : polynomial ℕ), ∀ x y, size (f x y) ≤ size y + p.eval (size x) := hf

theorem polysize_safe.iterate_invariant {f : α → β → β} {n : α → ℕ}  (inv : α → β → Prop)
  (hinv : ∀ x y, inv x y → inv x (f x y))
  (hf : ∃ (p : polynomial ℕ), ∀ x y, inv x y → size (f x y) ≤ size y + p.eval (size x))
  (hn : polysize_fun n) :
  ∃ p : mv_polynomial (fin 2) ℕ, ∀ x y (m ≤ n x), inv x y → size ((f x)^[m] y) ≤ mv_polynomial.eval ![size x, size y] p :=
begin
  cases hn with p hn, cases hf with q hf,
  use (mv_polynomial.X 1 + (polynomial.to_mv 0 p) * (polynomial.to_mv 0 q) : mv_polynomial (fin 2) ℕ),
  intros x y m hm hy, specialize hn x,
  have : ∀ n : ℕ, size ((f x)^[n] y) ≤ size y + n * (q.eval $ size x),
   { intro n, induction n with n ih generalizing y, 
    { simp, },
    rw [iterate_succ_apply, nat.succ_mul, nat.add_comm _ (q.eval (size x)), ← add_assoc],
    refine (ih _ $ hinv x y hy).trans _,
    simpa using hf x y hy, },
  refine (this $ m).trans _,
  simp, mono, exacts [hm.trans hn, zero_le'],
end

theorem polysize_safe.iterate {f : α → β → β} {n : α → ℕ}
  (hf : polysize_safe f) (hn : polysize_fun n) :
    ∃ p : mv_polynomial (fin 2) ℕ, ∀ x y (m ≤ n x), size ((f x)^[m] y) ≤ mv_polynomial.eval ![size x, size y] p :=
by simpa using polysize_safe.iterate_invariant (λ _ _, true) (λ _ _ _, trivial)
    ⟨hf.poly, λ x y _, hf.spec x y⟩ hn

theorem polysize_safe.comp {f : γ → δ → ε} {g : α → γ} {h : α → β → δ} :
  polysize_safe f → polysize_fun g → polysize_safe h → polysize_safe (λ x y, f (g x) (h x y))
| ⟨pf, hf⟩ ⟨pg, hg⟩ ⟨ph, hh⟩ :=
begin
  use ph + (pf.comp pg),
  intros x y,
  refine (hf _ _).trans _,
  simp [← add_assoc], mono*,
end

@[complexity] theorem polysize_safe.id : polysize_safe (λ _ : α, @id β) :=
⟨0, by simp⟩

@[complexity] theorem polysize_safe.id' : polysize_safe (λ (_ : α) (y : β), y) := polysize_safe.id

@[complexity] theorem polysize_safe.of_polysize_fun {f : α → γ} :
  polysize_fun f → polysize_safe (λ x (_ : β), f x)
| ⟨p, hp⟩ := ⟨p, λ x y, le_add_left (hp x)⟩

theorem polysize_safe.comp' {f : γ → δ} {g : α → β → γ}
  (hf : polysize_safe (λ (_ : unit) x, f x)) (hg : polysize_safe g) :
  polysize_safe (λ x y, f (g x y)) :=
hf.comp (show polysize_fun (default : α → unit), from ⟨0, by simp⟩) hg

@[complexity] theorem polysize_safe.cons {f : α → γ} {g : α → β → list γ} (hf : polysize_fun f) (hg : polysize_safe g) :
  polysize_safe (λ (x : α) (y : β), (f x) :: (g x y)) :=
by { apply polysize_safe.comp _ hf hg, use polynomial.X + 1, intros, apply le_of_eq, simp, abel, }

@[complexity] theorem polysize_safe.const (C : γ) : polysize_safe (λ (_ : α) (_ : β), C) :=
⟨polynomial.C (size C), λ x y, by simp⟩

@[complexity] theorem polysize_safe.fst {f : α → β → γ × δ} (hf : polysize_safe f) :
  polysize_safe (λ x y, (f x y).1) :=
by { refine polysize_safe.comp' _ hf, use 0, simp, }

@[complexity] theorem polysize_safe.snd {f : α → β → γ × δ} (hf : polysize_safe f) :
  polysize_safe (λ x y, (f x y).2) :=
by { refine polysize_safe.comp' _ hf, use 0, simp, }

@[complexity] theorem polysize_safe.some {f : α → β → γ} (hf : polysize_safe f) :
  polysize_safe (λ x y, some (f x y)) :=
by { refine polysize_safe.comp' _ hf, use 0, simp, }

@[complexity] theorem polysize_safe.pair_left {f : α → γ} {g : α → β → δ} :
  polysize_fun f → polysize_safe g → polysize_safe (λ x y, (f x, g x y))
| ⟨pf, hf⟩ ⟨pg, hg⟩ := ⟨pf + pg, λ x y, by { dsimp [has_uncurry.uncurry] at hf, simp, linarith only [hf x, hg x y], }⟩

@[complexity] theorem polysize_safe.pair_right {f : α → γ} {g : α → β → δ} :
  polysize_safe g → polysize_fun f → polysize_safe (λ x y, (g x y, f x))
|  ⟨pg, hg⟩ ⟨pf, hf⟩ := ⟨pf + pg, λ x y, by { dsimp [has_uncurry.uncurry] at hf, simp, linarith only [hf x, hg x y], }⟩

@[complexity] theorem polysize_safe.add_unary_left {f : α → ℕ} {g : α → β → ℕ} : 
  polysize_fun f → polysize_safe g → polysize_safe (λ x y, (f x) + (g x y))
| ⟨pf, hf⟩ ⟨pg, hg⟩ := ⟨pf + pg, λ x y, by { dsimp [has_uncurry.uncurry, polysize_unary_nat] at hf hg, simp, linarith only [hf x, hg x y], }⟩

@[complexity] theorem polysize_safe.add_unary_right {f : α → ℕ} {g : α → β → ℕ} :
  polysize_safe g → polysize_fun f → polysize_safe (λ x y, (g x y) + (f x))
| ⟨pg, hg⟩ ⟨pf, hf⟩ := ⟨pf + pg, λ x y, by { dsimp [has_uncurry.uncurry, polysize_unary_nat] at hf hg, simp, linarith only [hf x, hg x y], }⟩

@[complexity] theorem polysize_safe.ite {f g : α → β → γ} {P : α → β → Prop} [∀ x y, decidable (P x y)] (hf : polysize_safe f) (hg : polysize_safe g) :
  polysize_safe (λ x y, if P x y then f x y else g x y) :=
begin
  rcases hf with ⟨pf, hf⟩, rcases hg with ⟨pg, hg⟩, use pf + pg,
  intros x y, dsimp only, split_ifs,
  { refine (hf _ _).trans _, simp, }, { refine (hg _ _).trans _, simp, },
end

@[complexity] theorem polysize_safe.option_bind₁ {f : α → option γ} {g : α → β → γ → option δ} :
  polysize_fun f → polysize_safe (λ (usf : α × γ) (sf : β), g usf.1 sf usf.2) →
  polysize_safe (λ x y, (f x).bind (g x y))
| ⟨pf, hf⟩ ⟨pg, hg⟩ := ⟨pg.comp (polynomial.X + pf), λ x y, begin
  cases H : f x with v, { simp [H], },
  specialize hf x, simp only [H, has_uncurry.uncurry, id] at hf ⊢,
  refine (hg (x, v) y).trans _,
  simp, mono*,
end⟩

@[complexity] theorem polysize_safe.option_bind₂ {f : α → β → option γ} {g : α → γ → option δ} :
  polysize_safe f → polysize_safe g → polysize_safe (λ x y, (f x y).bind (g x))
| ⟨pf, hf⟩ ⟨pg, hg⟩ := ⟨pf + pg, λ x y, begin
  cases H : f x y with v, { simp [H], },
  specialize hf x y, 
  simp only [H, polysize.some_size, option.bind_some, polynomial.eval_add, ← add_assoc] at hf ⊢,
  exact (hg x v).trans (add_le_add_right hf _),
end⟩

@[complexity] theorem polysize_safe.option_map₁ {f : α → option γ} {g : α → β → γ → δ}
  (hf : polysize_fun f) (hg : polysize_safe (λ (usf : α × γ) (sf : β), g usf.1 sf usf.2)) :
  polysize_safe (λ x y, (f x).map (g x y)) :=
by { apply polysize_safe.option_bind₁ hf, exact polysize_safe.some hg, }

@[complexity] theorem polysize_safe.option_map₂ {f : α → β → option γ} {g : α → γ → δ}
  (hf : polysize_safe f) (hg : polysize_safe g) : polysize_safe (λ x y, (f x y).map (g x)) :=
by { apply polysize_safe.option_bind₂ hf, exact polysize_safe.some hg, }