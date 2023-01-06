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
  ) polytime'.nil' (by { simp, sorry, })).tail.init).of_eq $ λ v, begin
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

lemma polytime'_count_tt : polytime₁' (λ x, list.repeat tt (x.count tt)) :=
((polytime'.nth 0).foldl ((polytime'.nth 1).ite ((polytime'.nth 0).cons tt) (polytime'.nth 0)) polytime'.nil' 
  (by { simp, complexity, })).of_eq $ λ v,
by { simp, induction v.head using list.reverse_rec_on with l e ih, { simp, }, cases e; simp [*], }

lemma of_tree_polytime {f : tree unit → tree unit} (hf : tree.polytime f) :
  ∃ f' : list bool → list bool, polytime₁' f' ∧ ∀ (x : paren.dyck_words),
    f' ((↑x : list paren).map paren.to_bool) = (↑(tree.equiv_dyck_words $ f (tree.equiv_dyck_words.symm x)) : list paren).map paren.to_bool :=
begin
  induction hf,
  case tree.polytime.nil { sorry { refine ⟨λ _, [], polytime'.nil', _⟩, simp, } },
  case tree.polytime.id' { sorry { refine ⟨λ x, x, (polytime'.nth 0).of_eq _, _⟩; simp, } },
  case tree.polytime.left { sorry { refine ⟨_, polytime'_left, _⟩, simp, } },
  case tree.polytime.right { sorry { refine ⟨_, polytime'_right, _⟩, simp, } },
  case tree.polytime.pair : f g _ _ ihf ihg
  { sorry { rcases ihf with ⟨f', ihf, Hf⟩, rcases ihg with ⟨g', ihg, Hg⟩, 
    refine ⟨λ x, paren.up.to_bool :: (f' x) ++ paren.down.to_bool :: (g' x), 
      (ihf.cons paren.up.to_bool).append (ihg.cons paren.down.to_bool), _⟩,
    simp [Hf, Hg], } },
  case tree.polytime.comp : f g _ _ ihf ihg
  { sorry { rcases ihf with ⟨f', ihf, Hf⟩, rcases ihg with ⟨g', ihg, Hg⟩,
    refine ⟨λ x, f' (g' x), polytime'.comp (λ _ v, g' v.head) ihf (λ _, ihg), _⟩,
    simp [Hf, Hg], } },
  case tree.polytime.ite : f g h _ _ _ ihf ihg ihh
  { sorry { rcases ihf with ⟨f', ihf, Hf⟩, rcases ihg with ⟨g', ihg, Hg⟩, rcases ihh with ⟨h', ihh, Hh⟩,
    refine ⟨λ x, if (f' x).empty then g' x else h' x, ihf.ite_nil ihg ihh, _⟩,
    intro x, simp only [Hf],
    rcases f (tree.equiv_dyck_words.symm x) with (_|⟨⟨⟩, _, _⟩); simp [Hg, Hh], } },
  sorry,
end 

instance : tencodable paren := tencodable.of_equiv bool paren.to_bool

lemma _root_.polytime.equiv_dyck_words : (λ x : tree unit, (↑(tree.equiv_dyck_words x) : list paren)) ∈ₑ PTIME :=
begin
  complexity using λ x, x.stack_rec (λ _ : unit, []) (λ _ _ _, ()) (λ _ _ _, ())
    (λ ih₁ ih₂ _ _ _, paren.up :: (ih₁ ++ paren.down :: ih₂)) (),
  { use 1, simp [add_assoc], },
  induction x using tree.unit_rec_on; simp [*],
end

end polytime'
