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
| cases' {n f g h} :
  @polytime' (n+1) f → @polytime' (n+1) g → @polytime' (n+1) h →
  @polytime' (n+1) (λ v, @list.cases_on _ (λ _, list bool) v.head (f v) (λ hd tl, if hd then g v else h v))
| iter {n f} : @polytime' (n+2) f → 
  polysize_fun (λ v : vector (list bool) (n + 2), v.head.foldl (λ ls hd, f ([hd] ::ᵥ ls ::ᵥ v.tail.tail)) v.tail.head) →
  @polytime' (n+2) (λ v, v.head.foldl (λ ls hd, f ([hd] ::ᵥ ls ::ᵥ v.tail.tail)) v.tail.head)

namespace polytime'

theorem to_polytime {n f} (hf : @polytime' n f) : f ∈ₑ PTIME :=
begin
  induction hf,
  case polytime'.iter : n f hf hf' ih
  { sorry, },
  all_goals { sorry, }, -- complexity
end

lemma nth_one_eq_tail_head {α : Type*} {n} (v : vector α (n + 2)) :
  v.nth 1 = v.tail.head := by simp [← vector.nth_zero]

abbreviation polytime₁' (f : list bool → list bool) : Prop := @polytime' 1 (λ v, f v.head)
abbreviation polytime₂' (f : list bool → list bool → list bool) : Prop := @polytime' 2 (λ v, f v.head v.tail.head)

theorem of_eq {n} {f g : vector (list bool) n → list bool} (hf : polytime' f) (H : ∀ n, f n = g n) : polytime' g :=
(funext H : f = g) ▸ hf

theorem polytime'.cons {n f} (hf : @polytime' n f) (b : bool) : polytime' (λ v, b :: f v) :=
polytime'.comp (λ _ : fin 1, f) (polytime'.cons' b) (λ _, hf)

lemma cons₂_aux : polytime₂' (λ a b, a.head :: b) :=
(polytime'.cases' ((polytime'.nth 1).cons default) ((polytime'.nth 1).cons tt) ((polytime'.nth 1).cons ff)).of_eq $ λ n,
by rcases n.head with (_|⟨(_|_), tl⟩); simp [nth_one_eq_tail_head]

theorem polytime'.cons₂ {n f g} (hf : @polytime' n f) (hg : @polytime' n g) :
  polytime' (λ v, (f v).head :: g v) := polytime'.comp ![f, g] cons₂_aux (λ i, by fin_cases i; simpa)

theorem polytime'.foldl_of_eq {n ls f acc} (hls : @polytime' n ls) (hf : @polytime' (n + 2) f)
  (hacc : @polytime' n acc) {r : vector (list bool) n → list bool} (hr₁ : polysize_fun r)
  (hr₂ : ∀ v, r v = (ls v).foldl (λ acc' hd, f ([hd] ::ᵥ acc' ::ᵥ v)) (acc v)) :
  polytime' r :=
(polytime'.comp (fin.cons ls (fin.cons acc (λ i v, v.nth i))) hf (begin
  refine fin.cases _ _, { simpa, },
  refine fin.cases _ _, { simpa, },
  simpa using polytime'.nth,
end)).of_eq _

#check fin.cons_zero

theorem polytime'_reverse : @polytime' 1 (λ v, v.head.reverse) :=


-- Plan:
-- reverse
-- append
-- are_prefixes_nonneg -- 
-- is_balanced
-- left
-- drop
-- right

#check list


/-
There is a notion of `circuit computation`



-/