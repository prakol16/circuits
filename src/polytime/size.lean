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

@[simp] lemma size_list_fintype {α : Type*} [tencodable α] [fintype α] (x : list α) :
  size x = x.length := by simp [size]

lemma list.size_le_mul_of_le (a b : ℕ) (l : list α)
  (h₁ : l.length ≤ a) (h₂ : ∀ x ∈ l, size x ≤ b) :
  size l ≤ a * (b + 1) :=
begin
  simp only [size, add_comm b 1, mul_add, mul_one],
  refine add_le_add h₁ ((list.sum_le_card_nsmul _ b _).trans _),
  { simpa using h₂, }, { simpa using mul_le_mul_right' h₁ b, }
end

lemma list.perm.size_eq {l₁ l₂ : list α} (h : l₁ ~ l₂) : size l₁ = size l₂ :=
by simp only [size, h.length_eq, (h.map size).sum_eq]

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

instance {n : ℕ} : polysize (vector α n) :=
{ size := λ v, (v.map size).to_list.sum,
  upper := begin
    obtain ⟨p, hp⟩ := polysize.upper (list α),
    refine ⟨p, λ x, trans _ (hp x.to_list)⟩,
    simp only [size, vector.to_list_map],
    exact le_add_self,
  end,
  lower := begin
    obtain ⟨p, hp⟩ := polysize.lower (list α),
    refine ⟨p.comp (polynomial.C n + polynomial.X), λ x, (hp x.to_list).trans _⟩,
    simp [size],
  end }

lemma polysize_vector_def {n} (v : vector α n) : size v = (v.map size).to_list.sum := rfl

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

theorem polysize_fun.id : polysize_fun (@id α) := ⟨polynomial.X, by simp [has_uncurry.uncurry]⟩

theorem polysize_fun.comp {f : α → β} {g : γ → α} : polysize_fun f → polysize_fun g → polysize_fun (f ∘ g)
| ⟨p₁, h₁⟩ ⟨p₂, h₂⟩ := ⟨p₁.comp p₂, (λ x, by { rw polynomial.eval_comp, exact (h₁ (g x)).trans (p₁.eval_mono (h₂ x)), })⟩

theorem polysize_fun.head' : polysize_fun (@list.head' α) :=
⟨polynomial.X, λ x, by { cases x, { simp [has_uncurry.uncurry], }, simp [has_uncurry.uncurry, add_assoc], }⟩

theorem polysize_fun.tail : polysize_fun (@list.tail α) :=
⟨polynomial.X, λ x, by { cases x, { simp [has_uncurry.uncurry], }, simp [has_uncurry.uncurry], linarith only, }⟩

theorem polysize_fun.fst : polysize_fun (@prod.fst α β) :=
⟨polynomial.X, λ ⟨x, y⟩, by { simp [has_uncurry.uncurry], }⟩

theorem polysize_fun.snd : polysize_fun (@prod.snd α β) :=
⟨polynomial.X, λ ⟨x, y⟩, by { simp [has_uncurry.uncurry], }⟩

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

@[complexity] theorem polysize_safe.ordered_insert (r : α → γ → γ → Prop) [∀ x, decidable_rel (r x)] {f : α → γ} {g : α → β → list γ} (hf : polysize_fun f) (hg : polysize_safe g) :
  polysize_safe (λ x y, (g x y).ordered_insert (r x) (f x)) :=
by { cases hf with pf hf, cases hg with pg hg, use pg + pf + 1, intros x y, simp [← add_assoc, ((g x y).perm_ordered_insert (r x) (f x)).size_eq], rw add_comm, mono*, }

@[complexity] theorem polysize_safe.const (C : γ) : polysize_safe (λ (_ : α) (_ : β), C) :=
⟨polynomial.C (size C), λ x y, by simp⟩

@[complexity] theorem polysize_safe.fst {f : α → β → γ × δ} (hf : polysize_safe f) :
  polysize_safe (λ x y, (f x y).1) :=
by { refine polysize_safe.comp' _ hf, use 0, simp, }

@[complexity] theorem polysize_safe.left {f : α → β → tree unit} (hf : polysize_safe f) :
  polysize_safe (λ x y, (f x y).left) :=  
by { refine polysize_safe.comp' _ hf, use 0, simpa using tree.left_num_nodes_le, }

@[complexity] theorem polysize_safe.right {f : α → β → tree unit} (hf : polysize_safe f) :
  polysize_safe (λ x y, (f x y).right) :=  
by { refine polysize_safe.comp' _ hf, use 0, simpa using tree.right_num_nodes_le, }

@[complexity] theorem polysize_safe.snd {f : α → β → γ × δ} (hf : polysize_safe f) :
  polysize_safe (λ x y, (f x y).2) :=
by { refine polysize_safe.comp' _ hf, use 0, simp, }

@[complexity] theorem polysize_safe.some {f : α → β → γ} (hf : polysize_safe f) :
  polysize_safe (λ x y, some (f x y)) :=
by { refine polysize_safe.comp' _ hf, use 0, simp, }

@[complexity] theorem polysize_safe.tail {f : α → β → list γ} (hf : polysize_safe f) :
  polysize_safe (λ x y, (f x y).tail) :=
by { refine polysize_safe.comp' _ hf, use 0, rintros ⟨⟩ (_|⟨hd, tl⟩); simp, exact le_add_right le_add_self, }

@[complexity] theorem polysize_safe.head' {f : α → β → list γ} (hf : polysize_safe f) :
  polysize_safe (λ x y, (f x y).head') :=
by { refine polysize_safe.comp' _ hf, use 0, rintros ⟨⟩ (_|⟨hd, tl⟩); simp [add_assoc], }

@[complexity] theorem polysize_safe.head [inhabited γ] {f : α → β → list γ} (hf : polysize_safe f) :
  polysize_safe (λ x y, (f x y).head) :=
by { refine polysize_safe.comp' _ hf, use polynomial.C (size (default : γ)), rintros ⟨⟩ (_|⟨hd, tl⟩); simp [add_assoc], }

@[complexity] theorem polysize_safe.list_split [inhabited γ] {f : α → β → list γ} : polysize_safe f →
  polysize_safe (λ x y, ((f x y).head, (f x y).tail))
| ⟨p, hp⟩ := ⟨p + size (default : γ), λ x y, begin
  specialize hp x y,
  cases H : f x y, { simp [H, ← add_assoc], },
  simp [H] at hp ⊢, linarith only [hp],
end⟩ 

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

@[complexity] theorem polysize_safe.get_or_else {f : α → β → option γ} {g : α → β → γ} :
  polysize_safe f → polysize_safe g → polysize_safe (λ x y, (f x y).get_or_else (g x y))
| ⟨pf, hpf⟩ ⟨pg, hpg⟩ := ⟨pf + pg, λ x y, by { specialize hpf x y, cases H : f x y, { simp [H], linarith only [hpg x y], }, simp [H] at hpf ⊢, linarith only [hpf], }⟩

section comp
variables {α₀ α₁ α₂ α₃ α₄ α₅ α₆ : Type*}
  [tencodable α₀] [tencodable α₁] [tencodable α₂] [tencodable α₃] [tencodable α₄] [tencodable α₅] [tencodable α₆]
  [polysize α₀]   [polysize α₁]   [polysize α₂]   [polysize α₃]   [polysize α₄]   [polysize α₅]   [polysize α₆]

-- Convention: compₙ_i₁... means composition of `n`-ary function where i₁, i₂, are safe indices
-- TODO automate

theorem polysize_safe.comp₃_1 {f : α₀ → α₁ → α₂ → γ}
  {g₀ : α → α₀} {g₁ : α → β → α₁} {g₂ : α → α₂} :
  polysize_safe (λ (usf : α₀ × α₂) (sf : α₁), f usf.1 sf usf.2) → 
  polysize_fun g₀ → polysize_safe g₁ → polysize_fun g₂ →
  polysize_safe (λ x y, f (g₀ x) (g₁ x y) (g₂ x))
| ⟨pf, hf⟩ ⟨p₀, h₀⟩ ⟨p₁, h₁⟩ ⟨p₂, h₂⟩ := ⟨p₁ + pf.comp (p₀ + p₂), 
  λ x y, by { refine (hf (g₀ x, g₂ x) (g₁ x y)).trans _, simp [← add_assoc], mono*, }⟩

theorem polysize_safe.comp₃_2 {f : α₀ → α₁ → α₂ → γ}
  {g₀ : α → α₀} {g₁ : α → α₁} {g₂ : α → β → α₂} :
  polysize_safe (λ (usf : α₀ × α₁) (sf : α₂), f usf.1 usf.2 sf) → 
  polysize_fun g₀ → polysize_fun g₁ → polysize_safe g₂ →
  polysize_safe (λ x y, f (g₀ x) (g₁ x) (g₂ x y))
| ⟨pf, hf⟩ ⟨p₀, h₀⟩ ⟨p₁, h₁⟩ ⟨p₂, h₂⟩ := ⟨p₂ + pf.comp (p₀ + p₁), 
  λ x y, by { refine (hf (g₀ x, g₁ x) (g₂ x y)).trans _, simp [← add_assoc], mono*, }⟩

theorem polysize_safe.comp₄_1 {f : α₀ → α₁ → α₂ → α₃ → γ}
  {g₀ : α → α₀} {g₁ : α → β → α₁} {g₂ : α → α₂} {g₃ : α → α₃} :
  polysize_safe (λ (usf : α₀ × α₂ × α₃) (sf : α₁), f usf.1 sf usf.2.1 usf.2.2) → 
  polysize_fun g₀ → polysize_safe g₁ → polysize_fun g₂ → polysize_fun g₃ →
  polysize_safe (λ x y, f (g₀ x) (g₁ x y) (g₂ x) (g₃ x))
| ⟨pf, hf⟩ ⟨p₀, h₀⟩ ⟨p₁, h₁⟩ ⟨p₂, h₂⟩ ⟨p₃, h₃⟩ := ⟨p₁ + pf.comp (p₀ + p₂ + p₃), 
  λ x y, by { refine (hf (g₀ x, g₂ x, g₃ x) (g₁ x y)).trans _, simp [← add_assoc], mono*, }⟩

theorem polysize_safe.comp₄_2 {f : α₀ → α₁ → α₂ → α₃ → γ}
  {g₀ : α → α₀} {g₁ : α → α₁} {g₂ : α → β → α₂} {g₃ : α → α₃} :
  polysize_safe (λ (usf : α₀ × α₁ × α₃) (sf : α₂), f usf.1 usf.2.1 sf usf.2.2) → 
  polysize_fun g₀ → polysize_fun g₁ → polysize_safe g₂ → polysize_fun g₃ →
  polysize_safe (λ x y, f (g₀ x) (g₁ x) (g₂ x y) (g₃ x))
| ⟨pf, hf⟩ ⟨p₀, h₀⟩ ⟨p₁, h₁⟩ ⟨p₂, h₂⟩ ⟨p₃, h₃⟩ := ⟨p₂ + pf.comp (p₀ + p₁ + p₃), 
  λ x y, by { refine (hf (g₀ x, g₁ x, g₃ x) (g₂ x y)).trans _, simp [← add_assoc], mono*, }⟩


theorem polysize_safe.comp₄_3 {f : α₀ → α₁ → α₂ → α₃ → γ}
  {g₀ : α → α₀} {g₁ : α → α₁} {g₂ : α → α₂} {g₃ : α → β → α₃} :
  polysize_safe (λ (usf : α₀ × α₁ × α₂) (sf : α₃), f usf.1 usf.2.1 usf.2.2 sf) → 
  polysize_fun g₀ → polysize_fun g₁ → polysize_fun g₂ → polysize_safe g₃ →
  polysize_safe (λ x y, f (g₀ x) (g₁ x) (g₂ x) (g₃ x y))
| ⟨pf, hf⟩ ⟨p₀, h₀⟩ ⟨p₁, h₁⟩ ⟨p₂, h₂⟩ ⟨p₃, h₃⟩ := ⟨p₃ + pf.comp (p₀ + p₁ + p₂), 
  λ x y, by { refine (hf (g₀ x, g₁ x, g₂ x) (g₃ x y)).trans _, simp [← add_assoc], mono*, }⟩

theorem polysize_safe.comp₅_0 {f : α₀ → α₁ → α₂ → α₃ → α₄ → γ}
  {g₀ : α → β → α₀} {g₁ : α → α₁} {g₂ : α → α₂} {g₃ : α → α₃} {g₄ : α → α₄} :
  polysize_safe (λ (usf : α₁ × α₂ × α₃ × α₄) (sf : α₀), f sf usf.1 usf.2.1 usf.2.2.1 usf.2.2.2) → 
  polysize_safe g₀ → polysize_fun g₁ → polysize_fun g₂ → polysize_fun g₃ → polysize_fun g₄ →
  polysize_safe (λ x y, f (g₀ x y) (g₁ x) (g₂ x) (g₃ x) (g₄ x))
| ⟨pf, hf⟩ ⟨p₀, h₀⟩ ⟨p₁, h₁⟩ ⟨p₂, h₂⟩ ⟨p₃, h₃⟩ ⟨p₄, h₄⟩ := ⟨p₀ + pf.comp (p₁ + p₂ + p₃ + p₄),
  λ x y, by { refine (hf (g₁ x, g₂ x, g₃ x, g₄ x) (g₀ x y)).trans _, simp [← add_assoc], mono*, }⟩

theorem polysize_safe.comp₅_1 {f : α₀ → α₁ → α₂ → α₃ → α₄ → γ}
  {g₀ : α → α₀} {g₁ : α → β → α₁} {g₂ : α → α₂} {g₃ : α → α₃} {g₄ : α → α₄} :
  polysize_safe (λ (usf : α₀ × α₂ × α₃ × α₄) (sf : α₁), f usf.1 sf usf.2.1 usf.2.2.1 usf.2.2.2) → 
  polysize_fun g₀ → polysize_safe g₁ → polysize_fun g₂ → polysize_fun g₃ → polysize_fun g₄ →
  polysize_safe (λ x y, f (g₀ x) (g₁ x y) (g₂ x) (g₃ x) (g₄ x))
| ⟨pf, hf⟩ ⟨p₀, h₀⟩ ⟨p₁, h₁⟩ ⟨p₂, h₂⟩ ⟨p₃, h₃⟩ ⟨p₄, h₄⟩ := ⟨p₁ + pf.comp (p₀ + p₂ + p₃ + p₄),
  λ x y, by { refine (hf (g₀ x, g₂ x, g₃ x, g₄ x) (g₁ x y)).trans _, simp [← add_assoc], mono*, }⟩


end comp

@[complexity] theorem polysize_safe.list_cases_on {f : α → list γ} {g : α → β → δ}
  {h : α → β → γ → list γ → δ} (hf : polysize_fun f) (hg : polysize_safe g)
  (hh : polysize_safe (λ (usf : α × γ × list γ) (sf : β), h usf.1 sf usf.2.1 usf.2.2)) :
  @polysize_safe _ _ δ _ _ _ _ _ _ (λ x y, @list.cases_on _ (λ _, δ) (f x) (g x y) (h x y)) :=
begin
  convert_to polysize_safe (λ x y, ((f x).head'.map (λ hd, h x y hd (f x).tail)).get_or_else (g x y)),
  { ext x y, cases f x; simp, },
  refine polysize_safe.get_or_else _ hg,
  refine polysize_safe.option_map₁ (polysize_fun.head'.comp hf) _,
  exact hh.comp₄_1 polysize_fun.fst polysize_safe.id polysize_fun.snd
    (polysize_fun.tail.comp $ hf.comp polysize_fun.fst),
end
