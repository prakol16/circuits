import polytime.lemmas
import catalan

open_locale complexity_class
open_locale tree
open tencodable (encode)


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
  { apply polytime.list_foldl', rotate 3,
    { cases hf' with p hp, use p,
      rintro ⟨ls, v⟩, rcases v.exists_eq_cons with ⟨vhd, tl, rfl⟩, specialize hp (ls ::ᵥ tl),
      simp [function.has_uncurry.uncurry, polysize_vector_def] at hp ⊢,
      exact hp.trans (p.eval_mono $ add_le_add_left le_add_self _), },
    complexity, },
  complexity,
end

abbreviation polytime₁' (f : list bool → list bool) : Prop := @polytime' 1 (λ v, f v.head)
abbreviation polytime₂' (f : list bool → list bool → list bool) : Prop := @polytime' 2 (λ v, f v.head v.tail.head)

theorem of_eq {n} {f g : vector (list bool) n → list bool} (hf : polytime' f) (H : ∀ n, f n = g n) : polytime' g :=
(funext H : f = g) ▸ hf

def wrap1 {f} (hf : @polytime' 1 f) : polytime₁' (λ x, f (x ::ᵥ vector.nil)) :=
hf.of_eq $ λ v, by simp [vector.one_eq_head]

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

lemma _root_.vector.polysize_tail_le_self {α : Type*} [tencodable α] [polysize α] {n : ℕ} (v : vector α (n + 1)) :
  polysize.size v.tail ≤ polysize.size v :=
by { rcases v.exists_eq_cons with ⟨hd, tl, rfl⟩, simp [polysize_vector_def], }

theorem foldl' {n ls f acc} (hls : @polytime' n ls) (hf : @polytime' (n + 2) f)
  (hacc : @polytime' n acc)
  (hr : polysize_fun (λ v : vector (list bool) (n + 2), v.head.foldl (λ acc' hd, f (acc' ::ᵥ [hd] ::ᵥ v.tail.tail)) v.tail.head)) :
  polytime' (λ v, (ls v).foldl (λ acc' hd, f (acc' ::ᵥ [hd] ::ᵥ v)) (acc v)) :=
(polytime'.comp (fin.cons ls (fin.cons acc (λ i v, v.nth i))) (polytime'.fold hf hr) (begin
  refine fin.cases _ _, { simpa, },
  refine fin.cases _ _, { simpa, },
  simpa using polytime'.nth,
end)).of_eq $ λ v, by simp

protected theorem foldl {n ls f acc} (hls : @polytime' n ls) (hf : @polytime' (n + 2) f)
  (hacc : @polytime' n acc)
  (hr : polysize_safe (λ (usf : vector (list bool) n × bool) (sf : list bool), f (sf ::ᵥ [usf.2] ::ᵥ usf.1))) :
  polytime' (λ v, (ls v).foldl (λ acc' hd, f (acc' ::ᵥ [hd] ::ᵥ v)) (acc v)) :=
foldl' hls hf hacc begin
  apply polysize_safe.foldl, rotate 2,
  { cases hr with pr hr, use pr, rintro ⟨x, hd⟩ acc, specialize hr (x.tail.tail, hd) acc, 
    simp at hr ⊢, exact hr.trans (add_le_add_left (pr.eval_mono $ x.tail.polysize_tail_le_self.trans x.polysize_tail_le_self) _), },
  complexity,
end

theorem polytime'_reverse : @polytime' 1 (λ v, v.head.reverse) :=
((polytime'.nth 0).foldl ((polytime'.nth 1).cons₂ (polytime'.nth 0)) polytime'.nil' 
(by { simp, complexity, })).of_eq $ λ v, by { simp, rw [← list.foldr_reverse, list.foldr_eta], }

theorem reverse {n f} (hf : @polytime' n f) : polytime' (λ v, (f v).reverse) :=
polytime'.comp (λ _ : fin 1, f) polytime'_reverse (λ _, hf)

theorem polytime'_append : @polytime' 2 (λ v, v.head ++ v.tail.head) :=
((polytime'.nth 0).reverse.foldl ((polytime'.nth 1).cons₂ (polytime'.nth 0)) (polytime'.nth 1)
(by { simp, complexity, })).of_eq $ λ v, by { simp [vector.nth_one_eq_tail_head], induction v.head; simp [*], }

theorem append {n f g} (hf : @polytime' n f) (hg : @polytime' n g) : polytime' (λ v, (f v) ++ (g v)) :=
polytime'.comp ![f, g] polytime'_append (λ i, by fin_cases i; simpa)

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

theorem ite_head {n c f g} (hc : @polytime' n c) (b : bool) (hf : @polytime' n f) (hg : @polytime' n g) :
  polytime' (λ v, if (c v).head = b then f v else g v) :=
by { cases b, { refine (hc.ite hg hf).of_eq (λ v, _), cases (c v).head; simp, }, refine (hc.ite hf hg).of_eq (λ v, _), cases (c v).head; simp, }

theorem ite_len_eq {n c f g} (hc : @polytime' n c) (l : ℕ) (hf : @polytime' n f) (hg : @polytime' n g) :
  polytime' (λ v, if (c v).length = l then f v else g v) :=
begin
  induction l with l ih generalizing c, { refine (hc.ite_nil hf hg).of_eq _, simp [list.empty_iff_eq_nil, list.length_eq_zero], },
  refine (hc.ite_nil hg $ ih hc.tail).of_eq (λ v, _),
  cases c v; simp [nat.succ_eq_add_one, @eq_comm ℕ 0],
end

theorem ite_eq {n c f g} (hc : @polytime' n c) (x : list bool) (hf : @polytime' n f) (hg : @polytime' n g) :
  polytime' (λ v, if c v = x then f v else g v) :=
begin
  induction x with hd tl ih generalizing c, { refine (hc.ite_nil hf hg).of_eq _, simp [list.empty_iff_eq_nil], },
  refine (hc.ite_nil hg $ hc.ite_head hd (ih hc.tail) hg).of_eq (λ v, _),
  cases c v, { simp, }, { simp [ite_and], }
end

lemma polytime'_sum_parens : polytime₁' (λ x, list.repeat tt $ sum_parens (x.map paren.to_bool.symm)) :=
((polytime'.nth 0).foldl 
   ((polytime'.nth 0).ite_nil polytime'.nil' -- if acc = 0
      ((polytime'.nth 1).ite_head paren.up.to_bool -- if hd = paren.up
         ((polytime'.nth 0).cons tt) -- acc + 1
         ((polytime'.nth 0).tail))) -- acc - 1
   (polytime'.nil'.cons tt) -- [tt]
   (by { simp, complexity, })
  ).of_eq $ λ v, begin
  simp only [vector.nth_zero],
  induction v.head using list.reverse_rec_on with xs x ih, { simp [sum_parens], },
  rw [list.foldl_append, ih],
  simp [list.empty_iff_eq_nil, ← list.length_eq_zero, apply_ite (list.repeat tt), paren.to_bool.symm_apply_eq],
  refl,
end

lemma sum_parens {n f} (hf : @polytime' n f) : polytime' (λ v, list.repeat tt $ sum_parens ((f v).map paren.to_bool.symm)) :=
polytime'.comp (λ _ : fin 1, f) polytime'_sum_parens (λ _, hf)

lemma is_balanced {n f} (hf : @polytime' n f) : polytime' (λ v, [paren.are_heights_nonneg ((f v).map paren.to_bool.symm)]) :=
(hf.sum_parens.ite_len_eq 1 (polytime'.nil'.cons tt) (polytime'.nil'.cons ff)).of_eq $ λ v, begin
  by_cases H : paren.are_heights_nonneg ((f v).map paren.to_bool.symm); simp [is_balanced_iff, H],
end

lemma init {n f} (hf : @polytime' n f) : polytime' (λ v, (f v).init) :=
hf.reverse.tail.reverse.of_eq $ λ v, by induction f v using list.reverse_rec_on; simp

lemma polytime'_left : polytime₁' (λ x, (left_dyck_word $ x.map paren.to_bool.symm).map paren.to_bool) :=
((polytime'.nth 0).ite_nil polytime'.nil' $ 
  ((polytime'.nth 0).foldl (
    (polytime'.nth 0).ite_nil ((polytime'.nth 0).append $ polytime'.nth 1) $
    (polytime'.nth 0).is_balanced.ite (polytime'.nth 0) ((polytime'.nth 0).append $ polytime'.nth 1)
  ) polytime'.nil' (by { simp, complexity, })).tail.init).of_eq $ λ v, begin
  simp only [vector.nth_zero, list.empty_iff_eq_nil, left_dyck_word, list.map_eq_nil],
  split_ifs, { simp [left_dyck_word], },
  simp only [list.map_tail, list.map_init], congr,
  change _ = equiv_functor.map_equiv list paren.to_bool _, rw list.foldl_transport_equiv,
  simp [left_alg_foldl, list.empty_iff_eq_nil, equiv_functor.map, apply_ite (list.map paren.to_bool), ite_and],
end

lemma left {n f} (hf : @polytime' n f) : polytime' (λ v, (left_dyck_word $ (f v).map paren.to_bool.symm).map paren.to_bool) :=
polytime'.comp (λ _, f) polytime'_left (λ _, hf)

lemma polytime'_drop : @polytime' 2 (λ v, v.head.drop v.tail.head.length) :=
((polytime'.nth 1).foldl (polytime'.nth 0).tail (polytime'.nth 0) (by { simp, complexity, })).of_eq 
  (λ v, by simp [vector.nth_one_eq_tail_head])

lemma drop {n f g} (hf : @polytime' n f) (hg : @polytime' n g) :  polytime' (λ v, (f v).drop (g v).length) :=
polytime'.comp ![f, g] polytime'_drop $ λ i, by fin_cases i; simpa

lemma polytime'_right : polytime₁' (λ x, (right_dyck_word $ x.map paren.to_bool.symm).map paren.to_bool) :=
((polytime'.nth 0).drop (polytime'.nth 0).left).tail.tail.of_eq $ λ v, by { simp [right_dyck_word, list.map_drop, list.tail_drop], } 

lemma right {n f} (hf : @polytime' n f) : polytime' (λ v, (right_dyck_word $ (f v).map paren.to_bool.symm).map paren.to_bool) :=
polytime'.comp (λ _, f) polytime'_right (λ _, hf)

lemma polytime'_count_tt : polytime₁' (λ x, list.repeat tt (x.count tt)) :=
((polytime'.nth 0).foldl ((polytime'.nth 1).ite ((polytime'.nth 0).cons tt) (polytime'.nth 0)) polytime'.nil' 
  (by { simp, complexity, })).of_eq $ λ v,
by { simp, induction v.head using list.reverse_rec_on with l e ih, { simp, }, cases e; simp [*], }

lemma count_tt {n f} (hf : @polytime' n f) : polytime' (λ v, list.repeat tt $ (f v).count tt) :=
polytime'.comp (λ _, f) polytime'_count_tt (λ _, hf)

lemma iter {n f k s} (hf : polytime₁' f) (hk : @polytime' n k) (hs : @polytime' n s)
  (hf' : polysize_fun (λ (n : ℕ) (s : list bool), f^[n] s)) :
  polytime' (λ v, f^[(k v).length] (s v)) :=
(hk.foldl' (polytime'.comp _ hf (λ _, polytime'.nth 0)) hs begin
  simp only [vector.nth_cons_zero, vector.head_of_fn, list.foldl_eq_iterate],
  cases hf' with p hp, use p,
  rintro ⟨(_|⟨a, (_|⟨b, x⟩)⟩), hx⟩, iterate 2 { exfalso, refine absurd hx _, dec_trivial, },
  simp only [vector.head, vector.tail, polysize_vector_def, list.map, tree.polytime.uncurry_unary, size_list_fintype,
    vector.to_list_map, vector.to_list_mk, list.sum_cons, ← add_assoc],
  refine trans _ (p.eval_mono le_self_add),
  simpa [function.has_uncurry.uncurry] using hp (a.length, b),
end).of_eq $ λ v, by simp

-- We extract the inductive case of the iter step because it is large
lemma of_tree_polytime_iter_case (f : tree unit → tree unit) (hf : polysize_fun (λ x : tree unit, f^[x.left.num_nodes] x.right))
  (f' : list bool → list bool) (h₁ : polytime₁' f') (h₂ : ∀ (x : paren.dyck_words), 
    f' (list.map paren.to_bool ↑x) = list.map paren.to_bool ↑(tree.equiv_dyck_words (f (tree.equiv_dyck_words.symm x)))) :
  ∃ (g : list bool → list bool), polytime₁' g ∧ ∀ (x : paren.dyck_words), 
    g (list.map paren.to_bool ↑x) = list.map paren.to_bool ↑(tree.equiv_dyck_words (
      (λ x : tree unit, f^[x.left.num_nodes] x.right) (tree.equiv_dyck_words.symm x))) :=
begin
  set F : list bool → list bool := λ b, if paren.are_heights_nonneg (b.map paren.to_bool.symm) then f' b else [],
  have hF : ∀ (x : list bool) (n : ℕ), paren.are_heights_nonneg (x.map paren.to_bool.symm) → (F^[n] x) = (f'^[n] x),
  { rintros x n h,
    induction n with n ih generalizing x, { refl, },
    have : F x = f' x, { dsimp [F], simp [h], },
    rw [function.iterate_succ_apply, ih], { simp [this], },
    specialize h₂ ⟨_, h⟩, simp only [paren.coe_mk, list.map_map, equiv.self_comp_symm, list.map_id] at h₂, 
    simp [this, h₂], exact subtype.prop _, },
  have hF' : ∀ (x : list bool), ¬paren.are_heights_nonneg (x.map paren.to_bool.symm) → F x = [], { intros x H, dsimp [F], simp [H], },
  have hf' : ∀ (x : paren.dyck_words) (n : ℕ), (f'^[n] $ (↑x : list paren).map paren.to_bool) = 
    list.map paren.to_bool ↑(tree.equiv_dyck_words (f^[n] (tree.equiv_dyck_words.symm x))),
  { intros x n, induction n with n ih generalizing x, { simp, }, simp [ih, h₂], },
  have pF : polytime₁' F := ((polytime'.nth 0).is_balanced.ite h₁ polytime'.nil').of_eq (by simp), 
  refine ⟨_, (iter pF (polytime'.nth 0).left.count_tt (polytime'.nth 0).right _).wrap1, _⟩,
  { cases hf with pf hf,
    have : ∀ (n : ℕ) (b : list bool), paren.are_heights_nonneg (b.map paren.to_bool.symm) →
      (f'^[n] b).length ≤ 2 * pf.eval (n + b.length + 1),
    { intros n b hb, 
      suffices : (f'^[n] b).length ≤ 2 * pf.eval (n + b.length / 2 + 1), { refine this.trans _, mono*, exacts [nat.div_le_self _ _, zero_le'], },
      specialize hf' ⟨_, hb⟩ n, specialize hf ((encode n) △ tree.equiv_dyck_words.symm ⟨_, hb⟩),
      simp [tree.equiv_dyck_words_symm_num_nodes] at hf' hf,
      simpa [hf', tree.equiv_dyck_words_length] using hf, },
    use 2 * pf.comp (polynomial.X + 1), rintro ⟨n, b⟩,
    dsimp [function.has_uncurry.uncurry] at ⊢ hf,
    by_cases H : paren.are_heights_nonneg (b.map paren.to_bool.symm),
    { rw hF _ n H, simpa using this n _ H, },
    cases n,
    { have : b.length ≤ pf.eval (b.length + 1) := by simpa using (hf (tree.nil △ (encode b.length))),
      simp, linarith only [this], },
    rw [function.iterate_succ_apply, hF' _ H, hF [] n dec_trivial],
    specialize this n [] dec_trivial,
    simp, refine this.trans _, mono*, exacts [nat.le_succ _, zero_le', zero_le'], }, 
  intro x,
  simp only [vector.nth_cons_nil, list.map_map, equiv.symm_comp_self, list.count_map_of_equiv,
    list.map_id, left_dyck_word_spec, list.length_repeat, right_dyck_word_spec, tree.equiv_dyck_words_num_nodes_eq_count],
  rw [hF, hf'], { simp, }, simpa using x.right.prop,
end

lemma pair {n f g} (hf : @polytime' n f) (hg : @polytime' n g) : 
  polytime' (λ v, paren.up.to_bool :: (f v) ++ paren.down.to_bool :: (g v)) :=
(hf.cons paren.up.to_bool).append (hg.cons paren.down.to_bool)

lemma of_tree_polytime {f : tree unit → tree unit} (hf : tree.polytime f) :
  ∃ f' : list bool → list bool, polytime₁' f' ∧ ∀ (x : paren.dyck_words),
    f' ((↑x : list paren).map paren.to_bool) = (↑(tree.equiv_dyck_words $ f (tree.equiv_dyck_words.symm x)) : list paren).map paren.to_bool :=
begin
  induction hf,
  case tree.polytime.nil { { refine ⟨λ _, [], polytime'.nil', _⟩, simp, } },
  case tree.polytime.id' { { refine ⟨λ x, x, (polytime'.nth 0).of_eq _, _⟩; simp, } },
  case tree.polytime.left { { refine ⟨_, polytime'_left, _⟩, simp, } },
  case tree.polytime.right { { refine ⟨_, polytime'_right, _⟩, simp, } },
  case tree.polytime.pair : f g _ _ ihf ihg
  { { rcases ihf with ⟨f', ihf, Hf⟩, rcases ihg with ⟨g', ihg, Hg⟩, 
    refine ⟨_, (ihf.pair ihg).wrap1, _⟩,
    simp [Hf, Hg], } },
  case tree.polytime.comp : f g _ _ ihf ihg
  { { rcases ihf with ⟨f', ihf, Hf⟩, rcases ihg with ⟨g', ihg, Hg⟩,
    refine ⟨λ x, f' (g' x), polytime'.comp (λ _ v, g' v.head) ihf (λ _, ihg), _⟩,
    simp [Hf, Hg], } },
  case tree.polytime.ite : f g h _ _ _ ihf ihg ihh
  { { rcases ihf with ⟨f', ihf, Hf⟩, rcases ihg with ⟨g', ihg, Hg⟩, rcases ihh with ⟨h', ihh, Hh⟩,
    refine ⟨λ x, if (f' x).empty then g' x else h' x, ihf.ite_nil ihg ihh, _⟩,
    intro x, simp only [Hf],
    rcases f (tree.equiv_dyck_words.symm x) with (_|⟨⟨⟩, _, _⟩); simp [Hg, Hh], } },
  case tree.polytime.bounded_rec : f _ hf ih { rcases ih with ⟨f', h₁, h₂⟩, exact of_tree_polytime_iter_case f hf f' h₁ h₂, },
end

protected lemma const : ∀ (b : list bool), @polytime' 0 (λ _, b)
| [] := polytime'.nil
| (b :: xs) := (const xs).cons b

lemma const' {n : ℕ} (b : list bool) : @polytime' n (λ _, b) :=
polytime'.comp fin.elim0 (polytime'.const b) fin.elim0

lemma encode_bool {n f} (hf : @polytime' n f) : polytime' (λ v, list.map paren.to_bool ↑(tree.equiv_dyck_words (encode (f v).head))) :=
(hf.ite (const' $ list.map paren.to_bool ↑(tree.equiv_dyck_words (encode tt)))
  (const' $ list.map paren.to_bool ↑(tree.equiv_dyck_words (encode ff)))).of_eq $ λ v, by cases (f v).head; simp

instance : tencodable paren := tencodable.of_equiv bool paren.to_bool

lemma _root_.complexity_class.mem₂_iff {α β γ : Type} [tencodable α] [tencodable β] [tencodable γ]
  {f : α × β → γ} {C : complexity_class} : f ∈ₑ C ↔ (λ (x : α) (y : β), f (x, y)) ∈ₑ C :=
by { dsimp only [complexity_class.mem, function.has_uncurry.uncurry, id], simp only [prod.mk.eta], } 

lemma encode_list_aux : polytime₁' (λ b : list bool, list.map paren.to_bool ↑(tree.equiv_dyck_words (encode b))) :=
((polytime'.nth 0).reverse.foldl ((polytime'.nth 1).encode_bool.pair (polytime'.nth 0))
  nil' (begin
    simp, refine polysize_safe.cons _ (polysize_safe.append_left (polytime.size_le _) _), swap,
    { rw [complexity_class.mem₂_iff, complexity_class.mem.swap_args₂, complexity_class.iff_fintype],
      intro x, simpa [flip] using polytime.const _, },
    complexity,
  end)).of_eq $ λ v, begin
  simp only [list.head, list.map, vector.cons_cons_nth_one, vector.cons_head,
    vector.nth_cons_zero, list.cons_append, vector.nth_zero, list.foldl_reverse],
  induction v.head with hd tl ih, { simp [tencodable.encode_nil], },
  simp [ih, tencodable.encode_cons],
end

lemma encode_list {n f} (hf : @polytime' n f) : polytime' (λ v, list.map paren.to_bool ↑(tree.equiv_dyck_words (encode (f v)))) :=
polytime'.comp (λ _, f) encode_list_aux (λ _, hf)

lemma encode_vec : ∀ (n : ℕ), @polytime' n (λ v, list.map paren.to_bool ↑(tree.equiv_dyck_words (encode v)))
| 0 := (polytime'.const []).of_eq (λ v, by rw v.eq_nil; refl)
| (n + 1) := ((polytime'.nth 0).encode_list.pair (encode_vec n).vtail).of_eq 
  (λ v, by { conv_rhs { rw [← v.cons_head_tail, tencodable.encode_vec_cons], }, simp, })

lemma of_polytime_aux {n : ℕ} {α : Type} [tencodable α] {f : vector (list bool) n → α} :
  f ∈ₑ PTIME → polytime' (λ v, list.map paren.to_bool ↑(tree.equiv_dyck_words (encode $ f v)))
| ⟨f', pf, hf⟩ := let ⟨g, pg, hg⟩ := of_tree_polytime pf in by simpa [hg, hf] using polytime'.comp _ pg (λ _, encode_vec n)

@[complexity] lemma _root_.polytime_unary_nat_sum : (@list.sum ℕ _ _) ∈ₑ PTIME :=
by { delta list.sum, complexity, }

lemma _root_.list.iterate_append_nth_eq_self {α : Type*} (l : list α) (n : ℕ) :
  (λ x : list α, x ++ (l.nth x.length).to_list)^[n] [] = l.take n :=
begin
  induction n with n ih, { simp, },
  rw [function.iterate_succ_apply', ih, list.take_succ, list.length_take, min_def],
  split_ifs with h, { refl, },
  push_neg at h, rw [list.nth_eq_none_iff.mpr h.le, list.nth_eq_none_iff.mpr rfl.le],
end

lemma _root_.option.to_list_length_le_one {α : Type*} (l : option α) :
  l.to_list.length ≤ 1 := by cases l; simp [option.to_list]

lemma of_nth {n : ℕ} {f : vector (list bool) n → list bool}
  (h₁ : @polytime' (n + 1) (λ v, ((f v.tail).nth v.head.length).to_list))
  (h₂ : polysize_fun f) : polytime' f :=
begin
  cases h₂ with p hp, simp [polysize.size] at hp,
  obtain ⟨B, pB, hB⟩ : ∃ B : vector (list bool) n → list bool, polytime' B ∧
    ∀ v, (f v).length ≤ (B v).length,
  { refine ⟨_, of_polytime_aux (show (λ v : vector (list bool) n,
      p.eval (v.to_list.map list.length).sum) ∈ₑ PTIME, by complexity), λ v, (hp v).trans _⟩,
    simpa [tree.equiv_dyck_words_length] using nat.le_mul_of_pos_left (nat.zero_lt_succ _ : 0 < 2), }, 
  replace h₁ : polytime' (λ (v : vector (list bool) (n + 2)), ((f v.tail.tail).nth v.head.length).to_list),
  { refine (@polytime'.comp (n + 2) (n + 1) _ (by { refine fin.cases _ _, exacts [vector.head, λ n v, v.nth n.succ.succ], }) h₁ _).of_eq (λ v, _),
    { refine fin.cases _ _, { simpa using @polytime'.nth (n + 2) 0, }, { intro i, simpa using polytime'.nth _, }, },
    simp, congr, ext i : 1, simp, },
  refine (pB.foldl ((polytime'.nth 0).append h₁) polytime'.nil' _).of_eq (λ v, _),
  { simp, use 1, intros x y, simpa using option.to_list_length_le_one _, }, { simp [list.iterate_append_nth_eq_self, list.take_all_of_le (hB v)], },
end

lemma to_list {n : ℕ} {f : vector (list bool) n → option bool} (hf : f ∈ₑ PTIME) :
  polytime' (λ v, (f v).to_list) :=
((of_polytime_aux hf).ite_eq (list.map paren.to_bool ↑(tree.equiv_dyck_words (encode (none : option bool))))
  polytime'.nil' $
  (of_polytime_aux hf).ite_eq (list.map paren.to_bool ↑(tree.equiv_dyck_words (encode (some ff))))
  (polytime'.const' [ff]) (polytime'.const' [tt])).of_eq $ λ v, by rcases f v with (_|_|_); refl

@[complexity] lemma _root_.polytime.list_nth {α : Type} [tencodable α] : @list.nth α ∈ₑ PTIME :=
by { complexity using λ l n, (l.drop n).head', rw [← list.nth_zero, list.nth_drop], refl, }

@[complexity] lemma of_polytime {n : ℕ} {f : vector (list bool) n → list bool} (hf : f ∈ₑ PTIME) : polytime' f :=
of_nth (to_list $ by complexity) (polytime.size_le hf)

lemma iff_polytime {n : ℕ} {f : vector (list bool) n → list bool} :
  polytime' f ↔ f ∈ₑ PTIME := ⟨to_polytime, of_polytime⟩

lemma _root_.polytime.equiv_dyck_words : (λ x : tree unit, (↑(tree.equiv_dyck_words x) : list paren)) ∈ₑ PTIME :=
begin
  complexity using λ x, x.stack_rec (λ _ : unit, []) (λ _ _ _, ()) (λ _ _ _, ())
    (λ ih₁ ih₂ _ _ _, paren.up :: (ih₁ ++ paren.down :: ih₂)) (),
  { use 1, simp [add_assoc], },
  induction x using tree.unit_rec_on; simp [*],
end

end polytime'
