import complexity_class.stack_rec
import polytime.basic
import polytime.stack_rec_size

open tree (stack_step iterator_stack stack_step_polysize)
open tencodable function polysize

namespace polytime

open_locale complexity_class

variables {α β γ : Type} [tencodable α] [tencodable β] [tencodable γ]

section stack_rec

attribute [complexity] complexity_class.stack_iterate

variables {base : γ → α → β} {pre₁ pre₂ : γ → tree unit → tree unit → α → α}
  {post : γ → β → β → tree unit → tree unit → α → β}

@[complexity]
protected theorem stack_rec [polysize α] [polysize β] [polysize γ] {st : γ -> tree unit} {arg : γ → α} (hst : st ∈ₑ PTIME) (harg : arg ∈ₑ PTIME) (hb : base ∈ₑ PTIME) (hpr₁ : pre₁ ∈ₑ PTIME) (hpr₂ : pre₂ ∈ₑ PTIME) (hpo : post ∈ₑ PTIME)
  (hpr₁' : polysize_safe (λ (usf : γ × tree unit × tree unit) (sf : α), pre₁ usf.1 usf.2.1 usf.2.2 sf))
  (hpr₂' : polysize_safe (λ (usf : γ × tree unit × tree unit) (sf : α), pre₂ usf.1 usf.2.1 usf.2.2 sf))
  (hpo' : polysize_safe (λ (usf : γ × tree unit × tree unit × α) (sf : β × β), post usf.1 sf.1 sf.2 usf.2.1 usf.2.2.1 usf.2.2.2)) :
  polytime.mem (λ x : γ, (st x).stack_rec (base x) (pre₁ x) (pre₂ x) (post x) (arg x)) :=
begin
  suffices : polytime.mem (λ x, (stack_step (base x) (pre₁ x) (pre₂ x) (post x))^[(st x).time_steps] [sum.inl (st x, arg x, none)]),
  { rw complexity_class.of_some,
    convert complexity_class.mem.comp (show polytime.mem (λ x : list (iterator_stack α β), x.head'.bind sum.get_right), by complexity) this, 
    simp, },
  apply iterate, { dsimp only [tree.time_steps], complexity, }, { complexity, }, { complexity, },
  cases stack_step_polysize (polytime.size_le hst) (polytime.size_le harg)
    (polytime.size_le hb) hpr₁' hpr₂' hpo' with p hp,
  use p, intros x m _, exact hp x m,
end

lemma tree_eq : polytime.mem_pred (@eq (tree unit)) :=
begin
  rw ← complexity_class.mem_iff_mem_rel,
  complexity using λ x y, x.stack_rec (λ y' : tree unit, (y' = tree.nil : bool))
    (λ _ _ y', y'.left) (λ _ _ y', y'.right)
    (λ b₁ b₂ _ _ y, !(y = tree.nil : bool) && (b₁ && b₂)) y,
  { use 0, simpa using tree.left_num_nodes_le, }, { use 0, simpa using tree.right_num_nodes_le, }, { use 0, simp, },
  induction x using tree.unit_rec_on with l r ih₁ ih₂ generalizing y; cases y; simp [*],
end

@[complexity] lemma eq : (@eq α) ∈ₚ PTIME :=
by { have := tree_eq, complexity using (λ x y, encode x = encode y), simp, }

end stack_rec

section list

@[complexity] lemma list_len : (@list.length α) ∈ₑ PTIME :=
begin
  complexity using λ x, (encode x).stack_rec (λ _ : unit, 0) (λ _ _ _, ()) (λ _ _ _, ())
    (λ _ ih _ _ _, ih + 1) (),
  induction x with hd tl ih, { refl, },
  simpa [encode_cons],
end

@[simp] def scanl_step {α β : Type*} (f : β → α → β) : list α × list β → list α × list β
| ((x :: xs), (y :: ys)) := (xs, f y x :: y :: ys)
| x := x

@[complexity] theorem scanl_step_polytime {f : γ → β → α → β} {st : γ → list α × list β} (hf : f ∈ₑ PTIME) (hst : st ∈ₑ PTIME) :
  (λ x, scanl_step (f x) (st x)) ∈ₑ PTIME :=
by { delta scanl_step, clean_target, complexity, }

theorem scanl_step_iterate' {α : Type*} (f : β → α → β) (l : list α) (x : β) (n : ℕ) :
  (scanl_step f)^[n] (l, [x]) = (l.drop n, ((l.scanl f x).take (n + 1)).reverse) :=
begin
  suffices : ∀ xs, (scanl_step f)^[n] (l, x :: xs) = (l.drop n, ((l.scanl f x).take (n + 1)).reverse ++ xs),
  { simpa using this [], },
  intro xs,
  induction l with hd tl ih generalizing x xs n, { rw iterate_fixed; simp, },
  cases n, { simp, }, { simp [ih], },
end

theorem scanl_step_iterate {α : Type*} (f : β → α → β) (l : list α) (x : β) :
  (scanl_step f)^[l.length] (l, [x]) = ([], (l.scanl f x).reverse) :=
by { rw [scanl_step_iterate', ← @list.length_scanl _ _ f x l], simp, }

theorem foldl_size_le [polysize α] [polysize β] (f : β → α → β) (p : ℕ → ℕ) (hp : monotone p)
  (hf : ∀ x y, size (f x y) ≤ size x + p (size y)) (ls : list α) (x₀ : β) :
  size (ls.foldl f x₀) ≤ size x₀ + ls.length * p (size ls) :=
begin
  induction ls with hd tl ih generalizing x₀, { simp, },
  rw [list.foldl, list.length_cons, nat.succ_mul, ← add_assoc, add_right_comm],
  refine (ih _).trans (add_le_add ((hf _ _).trans $ add_le_add_left (hp _) _) (mul_le_mul_left' (hp _) _));
  simp; linarith only,
end

lemma list_scanl_rev [polysize α] [polysize β] [polysize γ] {lst : γ → list α} {acc : γ → β} {f : γ → β → α → β}
  (hlst : lst ∈ₑ PTIME) (hacc : acc ∈ₑ PTIME) (hf : f ∈ₑ PTIME)
  (hf' : polysize_safe (λ (usf : γ × α) (sf : β), f usf.1 sf usf.2)) :
  polytime.mem (λ x : γ, ((lst x).scanl (f x) (acc x)).reverse) :=
begin
  convert_to polytime.mem (λ x, ((scanl_step (f x))^[(lst x).length] (lst x, [acc x])).2),
  { simp [scanl_step_iterate], },
  refine complexity_class.mem.snd.comp _,
  apply iterate, complexity,
  cases hf' with pf hpf, cases polytime.size_le hlst with pl hpl, cases polytime.size_le hacc with pa hpa,
  use pl + (pl + 1) * (pa + pl * pf.comp (polynomial.X + pl) + 1),
  intros x m _,
  simp [scanl_step_iterate'], apply add_le_add,
  { exact (list.size_le_of_sublist ((lst x).drop_sublist _)).trans (hpl _), },
  refine (list.size_le_of_sublist (list.take_sublist _ _)).trans _,
  apply list.size_le_mul_of_le,
  { rw [list.length_scanl, add_le_add_iff_right], exact (lst x).length_le_size.trans (hpl _), },
  simp_rw list.mem_iff_nth_le,
  rintros e ⟨n, hn, rfl⟩,
  rw list.scanl_nth_le_eq_foldl,
  refine (foldl_size_le (f x) (λ a, pf.eval (size (x, a))) (λ a b h, pf.eval_mono $ add_le_add_left h _) (λ b a, hpf (x, a) b) _ _).trans _,
  simp, mono*,
  { exact min_le_of_right_le ((lst x).length_le_size.trans (hpl _)), },
  { exact (list.size_le_of_sublist (list.take_sublist _ _)).trans (hpl _), },
  exacts [zero_le', zero_le'],
end

@[complexity] lemma list_foldl [polysize α] [polysize β] [polysize γ] {lst : γ → list α} {acc : γ → β} {f : γ → β → α → β}
  (hlst : lst ∈ₑ PTIME) (hacc : acc ∈ₑ PTIME) (hf : f ∈ₑ PTIME)
  (hf' : polysize_safe (λ (usf : γ × α) (sf : β), f usf.1 sf usf.2)) :
  polytime.mem (λ x : γ, (lst x).foldl (f x) (acc x)) :=
begin
  rw complexity_class.of_some,
  convert complexity_class.head'.comp (list_scanl_rev hlst hacc hf hf'),
  ext x : 1, simp [list.scanl_last_eq_foldl],
end

@[complexity] theorem list_reverse : (@list.reverse α) ∈ₑ PTIME :=
begin
  complexity using (λ l : list α, l.foldl (λ (acc : list α) (hd : α), hd :: acc) []),
  rw [← list.foldr_reverse, list.foldr_eta],
end

@[complexity] lemma list_scanl [polysize α] [polysize β] [polysize γ] {lst : γ → list α} {acc : γ → β} {f : γ → β → α → β}
  (hlst : lst ∈ₑ PTIME) (hacc : acc ∈ₑ PTIME) (hf : f ∈ₑ PTIME)
  (hf' : polysize_safe (λ (usf : γ × α) (sf : β), f usf.1 sf usf.2)) :
  polytime.mem (λ x : γ, ((lst x).scanl (f x) (acc x))) :=
by simpa using list_reverse.comp (list_scanl_rev hlst hacc hf hf')

@[complexity] theorem list_foldr [polysize α] [polysize β] [polysize γ] {lst : γ → list α} {acc : γ → β} {f : γ → α → β → β}
  (hlst : lst ∈ₑ PTIME) (hacc : acc ∈ₑ PTIME) (hf : f ∈ₑ PTIME)
  (hf' : polysize_safe (λ (usf : γ × α) (sf : β), f usf.1 usf.2 sf)) :
  polytime.mem (λ x : γ, (lst x).foldr (f x) (acc x)) :=
by { simp_rw ← list.foldl_reverse, complexity, }

@[complexity] theorem list_map {lst : γ → list α} {f : γ → α → β} (hlst : lst ∈ₑ PTIME) (hf : f ∈ₑ PTIME) :
 (λ x, (lst x).map (f x)) ∈ₑ PTIME :=
by { complexity using (λ x, (lst x).foldr (λ hd acc, (f x hd) :: acc) []), induction lst x; simp [*], }

@[complexity] theorem list_all_some : (@list.all_some α) ∈ₑ PTIME :=
begin
  complexity using λ l, l.foldr (λ hd' acc', hd'.bind (λ hd, acc'.map (λ acc, hd :: acc))) (some []),
  induction l with hd, { simp, }, cases hd; simp [*],
end

instance {α : Type*} [polycodable α] : polycodable (list α) :=
{ poly := by { dunfold decode, complexity, } }

end list

end polytime