import polytime.lemmas
import catalan

open_locale complexity_class

inductive polytime' : ∀ {n : ℕ}, (vector (list bool) n → list bool) → Prop
| nil : @polytime' 0 (λ _, [])
| cons' (b : bool) : @polytime' 1 (λ v, b :: v.head)
| tail' : @polytime' 1 (λ v, v.head.tail)
| nth {n} (i : fin n) : polytime' (λ v, v.nth i)
| comp {m n f} (g : fin n → vector (list bool) m → list bool) :
    @polytime' n f → (∀ i, polytime' (g i)) → polytime' (λ a, f (vector.of_fn (λ i, g i a)))
| cases {n f g h} :
  @polytime' (n+1) f → @polytime' (n+1) g → @polytime' (n+1) h →
  @polytime' (n+1) (λ v, @list.cases_on _ (λ _, list bool) v.head (f v) (λ hd tl, if hd then g v else h v))
| fold {n f} : @polytime' (n+2) f → 
  polysize_fun (λ v : vector (list bool) (n + 2), v.head.foldl (λ ls hd, f (ls ::ᵥ [hd] ::ᵥ v.tail.tail)) v.tail.head) →
  @polytime' (n+2) (λ v, v.head.foldl (λ ls hd, f ( ls ::ᵥ [hd]  ::ᵥ v.tail.tail)) v.tail.head)

namespace polytime'

theorem to_polytime {n f} (hf : @polytime' n f) : f ∈ₑ PTIME :=
begin
  induction hf,
  case polytime'.fold : n f hf hf' ih
  { sorry, },
  all_goals { sorry, }, -- complexity
end

lemma _root_.vector.nth_one_eq_tail_head {α : Type*} {n} (v : vector α (n + 2)) :
  v.nth 1 = v.tail.head := by simp [← vector.nth_zero]

@[simp] lemma _root_.vector.cons_cons_nth_one {α : Type*} {n} (v : vector α n) (a b : α) :
  (a ::ᵥ b ::ᵥ v).nth 1 = b := by simp [vector.nth_one_eq_tail_head]

abbreviation polytime₁' (f : list bool → list bool) : Prop := @polytime' 1 (λ v, f v.head)
abbreviation polytime₂' (f : list bool → list bool → list bool) : Prop := @polytime' 2 (λ v, f v.head v.tail.head)

theorem of_eq {n} {f g : vector (list bool) n → list bool} (hf : polytime' f) (H : ∀ n, f n = g n) : polytime' g :=
(funext H : f = g) ▸ hf

lemma nil' {n : ℕ} : @polytime' n (λ v, []) :=
polytime'.comp fin.elim0 polytime'.nil fin.elim0

lemma cons {n f} (hf : @polytime' n f) (b : bool) : polytime' (λ v, b :: f v) :=
polytime'.comp (λ _, f) (polytime'.cons' b) (λ _, hf)

lemma polytime'_cons₂ : polytime₂' (λ a b, a.head :: b) :=
(polytime'.cases ((polytime'.nth 1).cons default) ((polytime'.nth 1).cons tt) ((polytime'.nth 1).cons ff)).of_eq $ λ n,
by rcases n.head with (_|⟨(_|_), tl⟩); simp [vector.nth_one_eq_tail_head]

lemma cons₂ {n f g} (hf : @polytime' n f) (hg : @polytime' n g) :
  polytime' (λ v, (f v).head :: g v) := polytime'.comp ![f, g] polytime'_cons₂ (λ i, by fin_cases i; simpa)

lemma tail {n f} (hf : @polytime' n f) : polytime' (λ v, (f v).tail) :=
polytime'.comp (λ _, f) polytime'.tail' (λ _, hf)

lemma vtail {n f} (hf : @polytime' n f) : @polytime' (n + 1) (λ v, f v.tail) :=
(polytime'.comp (λ (i : fin n) v, v.nth i.succ) hf (λ i, by simpa using polytime'.nth _)).of_eq (λ v, by { congr, ext i : 1, simp, })

protected theorem foldl {n ls f acc} (hls : @polytime' n ls) (hf : @polytime' (n + 2) f)
  (hacc : @polytime' n acc)
  (hr : polysize_fun (λ v : vector (list bool) (n + 2), v.head.foldl (λ acc' hd, f (acc' ::ᵥ [hd] ::ᵥ v.tail.tail)) v.tail.head)) :
  polytime' (λ v, (ls v).foldl (λ acc' hd, f (acc' ::ᵥ [hd] ::ᵥ v)) (acc v)) :=
(polytime'.comp (fin.cons ls (fin.cons acc (λ i v, v.nth i))) (polytime'.fold hf hr) (begin
  refine fin.cases _ _, { simpa, },
  refine fin.cases _ _, { simpa, },
  simpa using polytime'.nth,
end)).of_eq $ λ v, by simp

theorem polytime'_reverse : @polytime' 1 (λ v, v.head.reverse) :=
((polytime'.nth 0).foldl ((polytime'.nth 1).cons₂ (polytime'.nth 0)) polytime'.nil' 
(by { simp, complexity, })).of_eq $ λ v, by { simp, rw [← list.foldr_reverse, list.foldr_eta], }

theorem reverse {n f} (hf : @polytime' n f) : polytime' (λ v, (f v).reverse) :=
polytime'.comp (λ _ : fin 1, f) polytime'_reverse (λ _, hf)

theorem polytime'_append : @polytime' 2 (λ v, v.head ++ v.tail.head) :=
((polytime'.nth 0).reverse.foldl ((polytime'.nth 1).cons₂ (polytime'.nth 0)) (polytime'.nth 1)
(by { simp, complexity, })).of_eq $ λ v, by { simp [vector.nth_one_eq_tail_head], induction v.head; simp [*], }

theorem ite₃ {n c f g h} (hc : @polytime' n c) (hf : @polytime' n f) (hg : @polytime' n g)
  (hh : @polytime' n h) : polytime' (λ v, @list.cases_on _ (λ _, list bool) (c v) (f v) (λ hd _, if hd then g v else h v)) :=
(@polytime'.comp n (n + 1) _ (fin.cons c (λ i v, v.nth i)) 
  (polytime'.cases hf.vtail hg.vtail hh.vtail)
  (by { refine fin.cases _ _, simpa, simpa using polytime'.nth, })).of_eq $ λ v,
by { simp, congr, simp, }

theorem ite_nil {n c f g} (hc : @polytime' n c) (hf : @polytime' n f) (hg : @polytime' n g) :
  polytime' (λ v, if (c v).empty then f v else g v) :=
(hc.ite₃ hf hg hg).of_eq (λ v, by cases (c v); simp)

protected theorem ite {n c f g} (hc : @polytime' n c) (hf : @polytime' n f) (hg : @polytime' n g) :
  polytime' (λ v, if (c v).head then f v else g v) :=
(hc.ite₃ hg hf hg).of_eq $ λ v, by { rcases (c v) with (_|⟨hd, tl⟩); simp, }

theorem ite_eq {n c f g} (hc : @polytime' n c) (b : bool) (hf : @polytime' n f) (hg : @polytime' n g) :
  polytime' (λ v, if (c v).head = b then f v else g v) :=
by { cases b, { refine (hc.ite hg hf).of_eq (λ v, _), cases (c v).head; simp, }, refine (hc.ite hf hg).of_eq (λ v, _), cases (c v).head; simp, }

section sum_parens
/- In this section we describe an algorithm to count parentheses
  TODO: find cleaner/easier way and/or migrate this (which is all generic)
  to catalan.lean -/

def sum_parens (l : list bool) : list bool :=
l.foldl (λ (acc : list bool) (hd : bool), 
  if acc.empty then []
  else if hd = paren.up.to_bool then tt :: acc
  else acc.tail) [tt]

def sum_parens_len (l : list bool) := (sum_parens l).length

@[simp] lemma sum_parens_snoc (l : list bool) (b : bool) :
  sum_parens_len (l ++ [b]) = if sum_parens_len l = 0 then 0
    else if b = paren.up.to_bool then sum_parens_len l + 1 else sum_parens_len l - 1 := 
by simp [sum_parens, sum_parens_len, apply_ite list.length, list.empty_iff_eq_nil, ← list.length_eq_zero]

lemma mem_sum_parens {l : list bool} : ∀ {x : bool} (hx : x ∈ sum_parens l), x = tt :=
begin
  refine @list.foldl_rec_on _ _ (λ r, ∀ {x}, x ∈ r → x = tt) l (λ (acc : list bool) (hd : bool), _) _ _ _, { simp, },
  intros l ih _ _ b, dsimp only,
  split_ifs, { simp, }, { rintros (rfl|H), { refl, }, exact ih H, },
  intro H, exact ih (l.tail_subset H),
end

lemma sum_parens_eq_sum (x : list paren) (h : ∀ pfx, pfx <+: x → 0 ≤ (pfx.map paren.to_int).sum) :
  ((sum_parens_len (x.map paren.to_bool)) : ℤ) = (x.map paren.to_int).sum + 1 :=
begin
  induction x using list.reverse_rec_on with l e ih, { refl, },
  simp only [list.is_prefix_snoc_iff] at h,
  specialize ih (λ pfx hpfx, h _ (or.inr hpfx)),
  have : 0 < (sum_parens_len $ l.map paren.to_bool),
  { zify, rw ih, specialize h l (or.inr $ list.prefix_refl _), linarith only [h], },
  cases e; simp [ih, this.ne.symm, this],
end

lemma sum_parens_zero_of_pfx_zero {x r} (h : r <+: x) (h' : sum_parens_len r = 0) :
  sum_parens_len x = 0 :=
begin
  obtain ⟨x, rfl⟩ := h,
  induction x using list.reverse_rec_on with l e ih,
  { simpa using h', }, { simp [← list.append_assoc, ih], }
end

lemma sum_parens_matching_paren {x} (h : (paren.find_matching_paren x).is_some) :
  sum_parens_len (x.map paren.to_bool) = 0 :=
begin
  obtain ⟨r, h⟩ := option.is_some_iff_exists.mp h,
  apply sum_parens_zero_of_pfx_zero ((paren.find_matching_paren_is_prefx h).map paren.to_bool),
  have := sum_parens_eq_sum r.init (λ pfx, paren.sum_nonneg_of_pfx_init h),
  rw (paren.find_matching_paren_init h).2 at this, 
  rw ← list.init_append_last' _ (paren.find_matching_paren_last h),
  norm_cast at this,
  simp [this],
end

lemma is_balanced_iff (l : list paren) : paren.are_heights_nonneg l ↔ sum_parens_len (l.map paren.to_bool) = 1 :=
begin
  split,
  { intro h, rcases l with (_|⟨(hd|hd), tl⟩), { refl, }, 
    { have := sum_parens_eq_sum _ h.1, rw h.2 at this, simpa, },
    exfalso, exact paren.not_are_heights_nonnneg_down_cons _ h, },
  { rw paren.are_heights_nonneg, contrapose!,
    intros h₁ h₂,
    suffices : _, { refine h₁ this _, zify at h₂, rw sum_parens_eq_sum _ this at h₂, simpa using h₂, },
    contrapose! h₂,
    rw sum_parens_matching_paren, { trivial, },
    erw list.find_is_some, simpa using h₂, }
end

lemma is_balanced_iff' (l : list bool) : paren.are_heights_nonneg (l.map paren.to_bool.symm) ↔ sum_parens_len l = 1 :=
by simpa using is_balanced_iff (l.map paren.to_bool.symm)

end sum_parens

lemma polytime'_sum_parens : polytime₁' sum_parens :=
((polytime'.nth 0).foldl 
   ((polytime'.nth 0).ite_nil polytime'.nil' -- if acc.empty
      ((polytime'.nth 1).ite_eq paren.up.to_bool -- if hd = paren.up.to_bool
         ((polytime'.nth 0).cons tt) -- tt :: acc
         ((polytime'.nth 0).tail))) -- acc.tail
   (polytime'.nil'.cons tt) -- [tt]
   (by { simp, complexity, })
  ).of_eq $ λ v, by simp [sum_parens]


end polytime'

-- Plan:
-- reverse
-- append
-- are_prefixes_nonneg -- 
-- is_balanced
-- left
-- drop
-- right



/-
There is a notion of `circuit computation`



-/