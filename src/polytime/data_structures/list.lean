import polytime.lemmas
import complexity_class.dependent

namespace polytime

open_locale complexity_class
open tencodable function polysize

variables {α β γ δ ε η : Type} [tencodable α] [tencodable β] [tencodable γ]
 [tencodable δ] [tencodable ε] [tencodable η]

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

lemma list_scanl_rev' [polysize α] [polysize β] [polysize γ] {lst : γ → list α} {acc : γ → β} {f : γ → β → α → β}
  (hlst : lst ∈ₑ PTIME) (hacc : acc ∈ₑ PTIME) (hf : f ∈ₑ PTIME)
  (hf' : polysize_fun (λ (ls : list α) (x), ls.foldl (f x) (acc x))) :
  polytime.mem (λ x : γ, ((lst x).scanl (f x) (acc x)).reverse) :=
begin
  convert_to polytime.mem (λ x, ((scanl_step (f x))^[(lst x).length] (lst x, [acc x])).2),
  { simp [scanl_step_iterate], },
  refine complexity_class.mem.snd.comp _,
  apply iterate, complexity,
  cases hf' with pf hpf, cases polytime.size_le hlst with pl hpl,
  use pl + (pl + 1) * (pf.comp (pl + polynomial.X) + 1),
  intros x m _,
  simp [scanl_step_iterate'], apply add_le_add,
  { exact (list.size_le_of_sublist ((lst x).drop_sublist _)).trans (hpl _), },
  refine (list.size_le_of_sublist (list.take_sublist _ _)).trans _,
  apply list.size_le_mul_of_le,
  { rw [list.length_scanl, add_le_add_iff_right], exact (lst x).length_le_size.trans (hpl _), },
  simp_rw list.mem_iff_nth_le,
  rintros e ⟨n, hn, rfl⟩,
  rw list.scanl_nth_le_eq_foldl,
  exact (hpf ((lst x).take n, x)).trans (pf.eval_mono $ add_le_add_right ((list.size_le_of_sublist (list.take_sublist _ _)).trans (hpl _)) _),
end

lemma list_scanl_rev [polysize α] [polysize β] [polysize γ] {lst : γ → list α} {acc : γ → β} {f : γ → β → α → β}
  (hlst : lst ∈ₑ PTIME) (hacc : acc ∈ₑ PTIME) (hf : f ∈ₑ PTIME)
  (hf' : polysize_safe (λ (usf : γ × α) (sf : β), f usf.1 sf usf.2)) :
  polytime.mem (λ x : γ, ((lst x).scanl (f x) (acc x)).reverse) :=
list_scanl_rev' hlst hacc hf
  (polysize_safe.foldl polysize_fun.fst ((polytime.size_le hacc).comp polysize_fun.snd) 
    (by { apply hf'.comp₃_1, complexity, }))

lemma list_foldl' [polysize α] [polysize β] [polysize γ] {lst : γ → list α} {acc : γ → β} {f : γ → β → α → β}
  (hlst : lst ∈ₑ PTIME) (hacc : acc ∈ₑ PTIME) (hf : f ∈ₑ PTIME)
  (hf' : polysize_fun (λ (ls : list α) (x), ls.foldl (f x) (acc x))) :
  polytime.mem (λ x : γ, (lst x).foldl (f x) (acc x)) :=
begin
  rw complexity_class.of_some,
  convert complexity_class.head'.comp (list_scanl_rev' hlst hacc hf hf'),
  ext x : 1, simp [list.scanl_last_eq_foldl],
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

@[complexity] theorem list_tails : (@list.tails α) ∈ₑ PTIME :=
by { complexity using λ ls, ls.scanl (λ l _, l.tail) ls, induction ls; simp [*], }

@[complexity] theorem list_init : (@list.init α) ∈ₑ PTIME :=
by { complexity using λ ls, ls.reverse.tail.reverse, induction ls using list.reverse_rec_on; simp [list.init], }

theorem stack_rec_eq [inhabited β] [inhabited γ] (ls : list γ) (base : α → β) (pre : γ → list γ → α → α)
  (post : β → γ → list γ → α → β) (arg : α) : ls.stack_rec base pre post arg =
  (ls.tails.init.scanl (λ (acc : list γ × α) (x : list γ), (x.tail, pre x.head x.tail acc.2)) (ls, arg))
    .foldr (λ ls_arg ih, if ls_arg.1.empty then base ls_arg.2 else post ih ls_arg.1.head ls_arg.1.tail ls_arg.2) (arbitrary _) :=
begin
  induction ls with hd tl ih generalizing arg, { simp [list.init], },
  simp [list.init_cons_of_ne_nil (list.ne_nil_of_length_eq_succ $ list.length_tails _), ih],
end

@[complexity] theorem list_stack_rec [polysize α] [polysize β] [polysize γ] [polysize δ] {ls : δ → list γ} {base : δ → α → β} {pre : δ → γ → list γ → α → α}
  {post : δ → β → γ → list γ → α → β} {arg : δ → α} (hls : ls ∈ₑ PTIME) (hb : base ∈ₑ PTIME)
  (hpre : pre ∈ₑ PTIME) (hpost : post ∈ₑ PTIME) (harg : arg ∈ₑ PTIME)
  (hpre' : polysize_safe (λ (usf : δ × γ × list γ) (sf : α), pre usf.1 usf.2.1 usf.2.2 sf))
  (hpost' : polysize_safe (λ (usf : δ × γ × list γ × α) (sf : β), post usf.1 sf usf.2.1 usf.2.2.1 usf.2.2.2)) :
  (λ x, (ls x).stack_rec (base x) (pre x) (post x) (arg x)) ∈ₑ PTIME :=
begin
  casesI is_empty_or_nonempty δ, { exact complexity_class.of_from_fintype' _, },
  casesI is_empty_or_nonempty γ, { complexity using (λ x, base x (arg x)), cases ls x with hd, { refl, }, exact is_empty.elim' infer_instance hd, },
  inhabit δ, inhabit γ, haveI : inhabited α := ⟨arg default⟩, haveI : inhabited β := ⟨base default default⟩,
  simp_rw stack_rec_eq,
  complexity, { apply polysize_safe.comp₄_3, complexity, },
  { apply polysize_safe.comp₅_1, complexity, },
end

@[complexity] lemma repeat : (@list.repeat α) ∈ₑ PTIME :=
by { complexity using λ x n, (list.cons x)^[n] [], induction n; simp [iterate_succ', *], }

@[complexity] lemma nat_stack_rec {n : γ → ℕ} {base : γ → α → β} {pre : γ → ℕ → α → α} {post : γ → β → ℕ → α → β}
  {arg : γ → α}  (hn : n ∈ₑ PTIME) (hb : base ∈ₑ PTIME) (hpr : pre ∈ₑ PTIME) (hpo : post ∈ₑ PTIME)
  (harg : arg ∈ₑ PTIME) (hpr : polysize_safe (λ (usf : γ × ℕ) (sf : α), pre usf.1 usf.2 sf))
  (hpo' : polysize_safe (λ (usf : γ × ℕ × α) (sf : β), post usf.1 sf usf.2.1 usf.2.2)) : (λ x, (n x).stack_rec (base x) (pre x) (post x) (arg x)) ∈ₑ PTIME :=
begin
  complexity using λ x, (list.repeat () $ n x).stack_rec (base x) (λ _ tl y, pre x tl.length y)
    (λ ih _ tl y, post x ih tl.length y) (arg x),
  { apply polysize_safe.comp₃_2, complexity, },
  { apply polysize_safe.comp₄_1, complexity, },
  generalize : arg x = y, induction n x with n ih generalizing y,
  { simp, }, { simp [ih], },
end

@[complexity] lemma unary_nat_sum : (@list.sum ℕ _ _) ∈ₑ PTIME :=
by { delta list.sum, complexity, }

@[complexity] lemma list_ordered_insert {r : γ → α → α → Prop} [∀ x, decidable_rel (r x)] {a : γ → α} {ls : γ → list α} (hr : r ∈ₚ PTIME)
  (he : a ∈ₑ PTIME) (hls : ls ∈ₑ PTIME) : (λ x, (ls x).ordered_insert (r x) (a x)) ∈ₑ PTIME :=
begin
  complexity using λ x, (ls x).stack_rec (λ _ : unit, [a x]) (λ _ _ _, ())
    (λ ih b l _, if r x (a x) b then a x :: b :: l else b :: ih) (),
  induction ls x; simp [*],
end

@[complexity] lemma list_insertion_sort {r : γ → α → α → Prop} [∀ x, decidable_rel (r x)] {ls : γ → list α} (hr : r ∈ₚ PTIME)
  (hls : ls ∈ₑ PTIME) : (λ x, (ls x).insertion_sort (r x)) ∈ₑ PTIME :=
by { complexity using λ x, (ls x).foldr (λ b ih, list.ordered_insert (r x) b ih) [], induction ls x; simp [*], }

@[complexity] lemma list_append : ((++) : list α → list α → list α) ∈ₑ PTIME :=
by { complexity using λ l₁ l₂, l₁.foldr (λ hd acc, hd :: acc) l₂, induction l₁; simp [*], }

@[complexity] lemma list_drop : @list.drop α ∈ₑ PTIME :=
by { complexity using λ n l, list.tail^[n] l, simp, }

@[complexity] lemma list_any {l : α → list β} {p : α → β → bool} (hl : l ∈ₑ PTIME) (hp : p ∈ₑ PTIME) :
  (λ x, (l x).any (p x)) ∈ₑ PTIME :=
by { delta list.any, complexity, use 0, simp, }

@[complexity] lemma list_all {l : α → list β} {p : α → β → bool} (hl : l ∈ₑ PTIME) (hp : p ∈ₑ PTIME) :
  (λ x, (l x).all (p x)) ∈ₑ PTIME :=
by { delta list.all, complexity, use 0, simp, }

@[complexity] lemma list_bex {l : α → list β} {p : α → β → Prop} [∀ x y, decidable (p x y)] (hl : l ∈ₑ PTIME) (hp : p ∈ₚ PTIME) :
  (λ x, ∃ e ∈ l x, p x e) ∈ₚ PTIME :=
by { simp_rw [← list.any_iff_exists_prop], complexity, }

@[complexity] lemma list_ball {l : α → list β} {p : α → β → Prop} [∀ x y, decidable (p x y)] (hl : l ∈ₑ PTIME) (hp : p ∈ₚ PTIME) :
  (λ x, ∀ e ∈ l x, p x e) ∈ₚ PTIME :=
by { simp_rw ← list.all_iff_forall_prop, complexity, }

@[complexity] lemma list_mem : ((∈) : α → list α → Prop) ∈ₚ PTIME :=
by { haveI : decidable_eq α := decidable_eq_of_encodable _, complexity using λ x l, ∃ z ∈ l, z = x, simp, }

@[complexity] lemma pairwise {l : α → list β} {r : α → β → β → Prop} (hl : l ∈ₑ PTIME)
  (hr : r ∈ₚ PTIME) : (λ x, (l x).pairwise (r x)) ∈ₚ PTIME :=
begin
  classical, rw ← complexity_class.mem_iff_mem_pred,
  complexity using λ x, (l x).stack_rec (λ _ : unit, tt) (λ _ _ _, ())
    (λ ih hd tl _, (∀ a' ∈ tl, r x hd a') && ih) (), { use 0, simp, },
  induction l x; simp [*],
end

@[complexity] lemma list_nodup : (@list.nodup α) ∈ₚ PTIME :=
by { dunfold list.nodup, complexity, }

@[complexity] lemma list_nth {α : Type} [tencodable α] : @list.nth α ∈ₑ PTIME :=
by { complexity using λ l n, (l.drop n).head', rw [← list.nth_zero, list.nth_drop], refl, }

section dep
open_locale tree
variables {σ τ : α → Type} [∀ i, tencodable (σ i)] [∀ i, tencodable (τ i)]

lemma list_map_dep {f : ∀ x, list (σ x)} {g : ∀ x, σ x → τ x} (hf : f ∈ₐ PTIME) (hg : g ∈ₐ PTIME) :
  (λ x, @list.map _ (τ x) (g x) (f x)) ∈ₐ PTIME :=
polytime.functor_map_dep list hf hg (@list_map _ _ _ _ _ _) 

end dep

end polytime