import data.list.basic
import tree
import data.list.prod_sigma
import data.finset.basic
import data.finset.prod
import algebra.big_operators
import combinatorics.catalan
import tactic.derive_fintype
import data.nat.psub
import misc

namespace list
variables {α : Type*}

@[simp] lemma eq_self_append_iff {x y : list α} :
  x = x ++ y ↔ y = [] :=
⟨by simpa [eq_comm] using @append_left_cancel _ x [] y, λ h, by simp [h]⟩

@[simp] lemma inits_take (x : list α) (n : ℕ) :
  (x.take n).inits = x.inits.take (n + 1) :=
begin
  induction x with hd tl ih generalizing n, { simp, },
  cases n, { simp, },
  simp [ih, map_take],
end

@[simp] lemma take_succ_tail (x : list α) (n : ℕ) :
  (x.take (n+1)).tail = x.tail.take n :=
by cases x; simp

attribute [simp] prefix_cons_inj
@[simp] lemma prefix_cons_inj' {x y : α} {xs ys : list α} :
  (y :: ys) <+: (x :: xs) ↔ y = x ∧ ys <+: xs :=
by simp [is_prefix]

lemma is_prefix_cons_iff {x} {xs l : list α} :
  l <+: (x :: xs) ↔ l = [] ∨ ∃ l', l = x :: l' ∧ l' <+: xs :=
by { cases l with y ys, { simpa using list.nil_prefix _, }, simp [and_comm], }

@[simp] lemma is_prefix_snoc_iff {x} {xs l : list α} :
  l <+: xs ++ [x] ↔ l = xs ++ [x] ∨ l <+: xs :=
by simpa [← reverse_prefix, reverse_eq_iff] using @suffix_cons_iff _ l.reverse xs.reverse x

lemma is_prefix_append_iff {xs ys l : list α} :
  l <+: (xs ++ ys) ↔ l <+: xs ∨ ∃ l', l = xs ++ l' ∧ l' <+: ys :=
begin
  induction ys using list.reverse_rec_on with hd tl ih,
  { symmetry, revert l, simp, },
  simp_rw [← append_assoc, is_prefix_snoc_iff, ih],
  split,
  { rintro (rfl|H|⟨l', rfl, H⟩),
    exacts [or.inr ⟨hd ++ [tl], by simp⟩, or.inl H, or.inr ⟨l', ⟨rfl, or.inr H⟩⟩], },
  rintro (H|⟨l', rfl, rfl|H⟩),
  exacts [or.inr (or.inl H), (by simp), or.inr (or.inr ⟨l', rfl, H⟩)],
end

section
variables [has_one α] [has_mul α]

@[to_additive]
def prod_accuml (x : list α) : list α :=
x.inits.tail.map list.prod

@[simp, to_additive] lemma prod_accuml_len (x : list α) : x.prod_accuml.length = x.length :=
by simp [prod_accuml]

@[simp, to_additive] lemma prod_accuml_nil_iff {x : list α} : x.prod_accuml = [] ↔ x = [] :=
by simp [← length_eq_zero]

@[simp, to_additive] lemma prod_accuml_nil : (@list.nil α).prod_accuml = [] := rfl

end

section
variables [comm_monoid α]

@[simp, to_additive] lemma prod_accuml_cons (x : α) (xs : list α) :
  (x :: xs).prod_accuml = x :: xs.prod_accuml.map (*x) :=
by cases xs; simp [prod_accuml, function.comp, mul_comm]

@[simp, to_additive] lemma prod_accuml_singleton (x : α) : [x].prod_accuml = [x] :=
by simp [prod_accuml]

@[simp, to_additive] lemma prod_accuml_append (xs ys : list α) :
  (xs ++ ys).prod_accuml = xs.prod_accuml ++ ys.prod_accuml.map (*xs.prod) :=
begin
  simp only [prod_accuml, inits_append, map_tail, map_append, map_map],
  rw tail_append_of_ne_nil, swap, { simp [← length_eq_zero], },
  congr' 3, ext ys, simp [mul_comm],
end

@[to_additive] lemma prod_accuml_last {x : list α} {p : α} (hp : p ∈ x.prod_accuml.last') :
  p = x.prod :=
begin
  induction x using list.reverse_rec_on, { contradiction, },
  simpa [mul_comm, eq_comm] using hp,
end

@[to_additive] lemma prod_accuml_last_of_ne_nil {x : list α} (hx : x ≠ []) :
  x.prod_accuml.last' = some x.prod :=
by { induction x using list.reverse_rec_on, { contradiction, }, simp [mul_comm, eq_comm], }

@[simp, to_additive] lemma prod_take (x : list α) (n : ℕ) :
  (x.take n).prod_accuml = x.prod_accuml.take n :=
by simp [prod_accuml, map_take]

end

@[simp] lemma find_append_eq_orelse (x y : list α) (p : α → Prop) [decidable_pred p] :
  (x ++ y).find p = (x.find p).orelse (y.find p) :=
begin
  induction x with hd tl ih, { simp, },
  by_cases H : p hd,
  { simp [H], }, { simpa [H], }
end

lemma find_append {x : list α} {r} {p : α → Prop} [decidable_pred p] (hx : x.find p = some r)
  (y : list α) : (x ++ y).find p = some r := by simp [hx]

@[simp] lemma find_singleton (x : α) (p : α → Prop) [decidable_pred p] :
  [x].find p = option.guard p x :=
by by_cases H : p x; simp [H, option.guard]

section
variables {x : list α} {p : list α → Prop} [decidable_pred p]

lemma find_prefix_is_prefix {r} (h : x.inits.find p = some r) : r <+: x :=
by simpa using find_mem h

lemma find_prefix_is_min {r r'} (h : x.inits.find p = some r) (hr₁ : r' <+: r)
  (hr₂ : p r') : r' = r :=
begin
  induction x using list.reverse_rec_on with it lt ih generalizing r r',
  { cases mem_singleton.mp (find_mem h), simpa using hr₁, },
  simp only [inits, map, inits_append, tail_cons, find_append_eq_orelse, find_singleton] at h,
  cases H : it.inits.find p with r₀, swap,
  { cases (show r₀ = r, by simpa [H] using h), exact ih H hr₁ hr₂, },
  obtain ⟨rfl, h⟩ : it ++ [lt] = r ∧ p (it ++ [lt]) := by { simpa [H] using h, },
  rcases list.is_prefix_snoc_iff.mp hr₁ with rfl|hr₁, { refl, },
  exact absurd hr₂ (find_eq_none.mp H _ $ by simpa),
end

lemma _root_.option.is_some_iff_ne_none {x : option α} :
  x.is_some ↔ x ≠ none :=
by cases x; simp

@[simp] lemma find_is_some {p : α → Prop} [decidable_pred p] :
  (x.find p).is_some ↔ ∃ e ∈ x, p e :=
by simpa [-find_eq_none, option.is_some_iff_ne_none] using (@find_eq_none _ p _ x).not

end

end list

open_locale tree

namespace tree

@[simp] lemma height_eq_zero_iff {x : tree unit} : x.height = 0 ↔ x = nil :=
by cases x; simp [height]

end tree

@[derive [fintype, decidable_eq]]
inductive paren
| up | down

namespace paren

instance : inhabited paren := ⟨up⟩

@[irreducible] def to_bool : paren ≃ bool :=
{ to_fun := λ x, by { cases x, exacts [ff, tt] },
  inv_fun := λ x, by { cases x, exacts [up, down] },
  left_inv := λ x, by cases x; refl,
  right_inv := λ x, by cases x; refl }

@[simp] def to_int : paren → ℤ
| up := 1
| down := -1

def are_heights_nonneg (x : list paren) : Prop :=
(∀ pfx, pfx <+: x → 0 ≤ (pfx.map to_int).sum) ∧ (x.map to_int).sum = 0

instance : decidable_pred are_heights_nonneg := λ x,
decidable_of_iff ((∀ (pfx : list paren), pfx ∈ x.inits → 0 ≤ (pfx.map to_int).sum) ∧ (x.map to_int).sum = 0) (by simp; refl)

lemma are_heights_nonneg_iff {x : list paren} :
  are_heights_nonneg x ↔ (∀ sfx, sfx <:+ x → (sfx.map to_int).sum ≤ 0) ∧ (x.map to_int).sum = 0 :=
begin
  split;
  { rintro ⟨h₁, h₂⟩, refine ⟨_, h₂⟩,
    rintros sfx ⟨pfx, rfl⟩,
    simp at h₂,
    linarith [h₁ pfx ⟨_, rfl⟩], },
end

lemma _root_.forall_eq₂ {α β : Type*} {p : α → β → Prop} {f : β → α} :
  (∀ x y, x = f y → p x y) ↔ ∀ y, p (f y) y := by { tidy, subst_vars, tidy, }

lemma are_heights_nonneg_append {x y : list paren} (hx : are_heights_nonneg x) (hy : are_heights_nonneg y) :
  are_heights_nonneg (x ++ y) :=
by simpa [are_heights_nonneg, list.is_prefix_append_iff, or_imp_distrib, forall_and_distrib,
    forall_eq₂, hx.2, hy.2] using and.intro hx.1 hy.1

lemma are_heights_nonneg_surround {x : list paren} (hx : are_heights_nonneg x) :
  are_heights_nonneg (up :: x ++ [down]) :=
begin
  have : ∀ a, a <+: x → 0 ≤ 1 + (a.map to_int).sum := λ a ha, le_add_of_le_of_nonneg zero_le_one (hx.1 a ha),
  simpa [are_heights_nonneg, list.is_prefix_cons_iff, forall_eq₂, hx.2],
end

def find_matching_paren (x : list paren) : option (list paren) :=
x.inits.find (λ pfx : list paren, (pfx.map to_int).sum < 0)

@[simp] lemma find_matching_paren_nil : find_matching_paren [] = none := rfl

lemma find_matching_paren_is_prefx {x r} (hr : find_matching_paren x = some r) : r <+: x :=
by simpa using list.find_mem hr

lemma sum_nonneg_of_pfx_match_paren {x r pfx} (hr : find_matching_paren x = some r)
  (h₁ : pfx <+: r) (h₂ : pfx ≠ r) : 0 ≤ (pfx.map to_int).sum :=
by { contrapose! h₂, exact list.find_prefix_is_min hr h₁ h₂, }

lemma find_matching_paren_last {x r} (hr : find_matching_paren x = some r) :
  r.last' = some down :=
begin
  induction r using list.reverse_rec_on with it lt,
  { exfalso, simpa using list.find_some hr, },
  cases lt, swap, { simp, },
  exfalso,
  have : (it.map to_int).sum + 1 < 0 := by simpa using list.find_some hr,
  linarith [sum_nonneg_of_pfx_match_paren hr ⟨[up], rfl⟩ (by simp)],
end

lemma sum_nonneg_of_pfx_init {x r pfx} (hr : find_matching_paren x = some r)
  (h : pfx <+: r.init) : 0 ≤ (pfx.map to_int).sum :=
begin
  refine sum_nonneg_of_pfx_match_paren hr (h.trans $ list.init_prefix _) _,
  rintro rfl, have := h.length_le,
  rw ← list.init_append_last' _ (find_matching_paren_last hr) at this,
  simpa,
end

lemma find_matching_paren_init {x r} (hr : find_matching_paren x = some r) :
  are_heights_nonneg r.init :=
begin
  refine ⟨λ pfx, sum_nonneg_of_pfx_init hr, le_antisymm _ (sum_nonneg_of_pfx_init hr (by refl))⟩,
  have := list.find_some hr, rw ← list.init_append_last' _ (find_matching_paren_last hr) at this,
  simpa [← @int.lt_add_one_iff _ 0],
end

lemma find_matching_paren_sum {x r} (hr : find_matching_paren x = some r) :
  (r.map to_int).sum = -1 :=
by { rw ← list.init_append_last' _ (find_matching_paren_last hr), simpa using (find_matching_paren_init hr).2, }

lemma find_matching_paren_suffx {x r} (hx : are_heights_nonneg (up :: x))
  (hr : find_matching_paren x = some r) : are_heights_nonneg (x.drop r.length) :=
begin
  rcases find_matching_paren_is_prefx hr with ⟨s, rfl⟩,
  rcases are_heights_nonneg_iff.mp hx with ⟨hx₁, hx₂⟩, rw are_heights_nonneg_iff,
  split,
  { exact λ sfx H, hx₁ sfx (H.trans ⟨up :: r, by simp⟩), },
  { simpa [find_matching_paren_sum hr] using hx₂, },
end

lemma find_matching_paren_is_some {x} (hx : are_heights_nonneg (up :: x)) :
  (find_matching_paren x).is_some :=
by { erw list.find_is_some, refine ⟨x, by simp, _⟩, have := hx.2, simp at this, linarith, }

lemma not_are_heights_nonnneg_down_cons (x) : ¬are_heights_nonneg (down :: x) | p :=
absurd (p.1 [down] ⟨x, rfl⟩) dec_trivial

lemma surround_append {x r} (hr : find_matching_paren x = some r) :
  r.init ++ down :: (x.drop r.length) = x :=
begin
  rcases find_matching_paren_is_prefx hr with ⟨y, rfl⟩,
  simpa using congr_arg (++y) (list.init_append_last' _ (find_matching_paren_last hr)),
end

lemma find_paren_nonneg {x} (h : are_heights_nonneg x) :
  find_matching_paren x = none := by simpa [find_matching_paren] using h.1

lemma find_matching_paren_append {x r} (hx : find_matching_paren x = some r) (y) :
  find_matching_paren (x ++ y) = some r :=
by simp [find_matching_paren, -list.find_append_eq_orelse, list.find_append hx]

lemma find_paren_append {x y} (h : are_heights_nonneg x) :
  find_matching_paren (x ++ down :: y) = some (x ++ [down]) :=
begin
  induction y using list.reverse_rec_on with it lt ih,
  { have := find_paren_nonneg h, rw [find_matching_paren] at this,
    simp [find_matching_paren, this, h.2], },
  simpa using find_matching_paren_append ih [lt],
end

def dyck_words := {l // are_heights_nonneg l}

instance : has_lift dyck_words (list paren) := ⟨λ x, x.val⟩

@[simp] lemma coe_mk (l : list paren) (p : are_heights_nonneg l) : ↑(⟨l, p⟩ : dyck_words) = l := rfl

def dyck_words.nil : dyck_words := ⟨[], by simp [are_heights_nonneg]⟩
@[simp] lemma dyck_words.nil_val : (↑dyck_words.nil : list paren) = [] := rfl

def dyck_words.append (x y : dyck_words) : dyck_words := ⟨_, are_heights_nonneg_append x.prop y.prop⟩
instance : has_append dyck_words := ⟨dyck_words.append⟩

@[simp] lemma dyck_words.append_val (x y : dyck_words) : (↑(x ++ y) : list paren) = ↑x ++ ↑y := rfl

def dyck_words.surround (x : dyck_words) : dyck_words := ⟨_, are_heights_nonneg_surround x.prop⟩
@[simp] lemma dyck_words.surround_val (x : dyck_words) :
  (↑x.surround : list paren) = up :: ↑x ++ [down] := rfl

section cases_on
variables {motive : dyck_words → Sort*} (x : dyck_words) (nil : motive dyck_words.nil)
  (cons_up : ∀ (xs : list paren) (p : are_heights_nonneg (up :: xs)), motive ⟨_, p⟩)
include nil cons_up

@[elab_as_eliminator]
def dyck_words.cases_on : motive x :=
begin
  rcases x with ⟨_|⟨_|_, xs⟩, p⟩,
  exacts [nil, cons_up xs p, absurd (p.1 [down] ⟨xs, rfl⟩) dec_trivial],
end

@[simp] lemma dyck_words.nil_cases_on : dyck_words.nil.cases_on nil cons_up = nil := rfl

end cases_on

def dyck_words.left : dyck_words → dyck_words
| ⟨[], p⟩ := dyck_words.nil
| ⟨(down :: xs), p⟩ := absurd (p.1 [down] ⟨xs, rfl⟩) dec_trivial
| ⟨(up :: xs), p⟩ :=
⟨(option.get (find_matching_paren_is_some p)).init, find_matching_paren_init (option.some_get _).symm⟩

@[simp] lemma dyck_words.left_nil : dyck_words.nil.left = dyck_words.nil := rfl

instance : decidable_eq dyck_words := subtype.decidable_eq

def dyck_words.right : dyck_words → dyck_words
| ⟨[], p⟩ := dyck_words.nil
| ⟨(down :: xs), p⟩ := absurd (p.1 [down] ⟨xs, rfl⟩) dec_trivial
| ⟨(up :: xs), p⟩ :=
⟨xs.drop (option.get (find_matching_paren_is_some p)).length,
find_matching_paren_suffx p (option.some_get _).symm⟩

lemma dyck_words_eq_self {x : dyck_words} (hx : x ≠ dyck_words.nil) :
  x.left.surround ++ x.right = x :=
begin
  ext : 1,
  induction x using paren.dyck_words.cases_on with xs p, { contradiction, },
  simpa [dyck_words.left, dyck_words.right] using surround_append (option.some_get _).symm,
end

@[simp] lemma dyck_words_left (x y : dyck_words) : (x.surround ++ y).left = x :=
begin
  induction H : (x.surround ++ y) using paren.dyck_words.cases_on;
    apply_fun (coe : dyck_words → list paren) at H,
  { exfalso, simpa using H, },
  have : xs = ↑x ++ (down :: ↑y), { simpa [eq_comm] using H, },
  ext : 1, simp [dyck_words.left, this, find_paren_append x.prop, list.init],
end

lemma dyck_words.append_right_injective (y : dyck_words) : function.injective (λ x, y ++ x) :=
λ x₁ x₂ h,
by { ext : 1, apply_fun (coe : _ → list paren) at h, simpa [list.append_right_inj] using h, }

@[simp] lemma dyck_words.append_right_inj {y x₁ x₂ : dyck_words} : y ++ x₁ = y ++ x₂ ↔ x₁ = x₂ :=
(dyck_words.append_right_injective y).eq_iff

@[simp] lemma dyck_words.nil_right : dyck_words.nil.right = dyck_words.nil := rfl

@[simp] lemma dyck_words_right (x y : dyck_words) : (x.surround ++ y).right = y :=
begin
  have := @dyck_words_eq_self (x.surround ++ y) _, { simpa, },
  apply_fun (coe : dyck_words → list paren), simp,
end

lemma dyck_words.left_lt {x : dyck_words} (hx : x ≠ dyck_words.nil) :
  (↑x.left : list paren).length < (↑x : list paren).length :=
by { conv_rhs { rw ← dyck_words_eq_self hx, }, simp [add_assoc], }

lemma dyck_words.right_lt {x : dyck_words} (hx : x ≠ dyck_words.nil) :
  (↑x.right : list paren).length < (↑x : list paren).length :=
by { conv_rhs { rw ← dyck_words_eq_self hx, }, simp, linarith, }

instance : has_sizeof dyck_words := ⟨λ x, (↑x : list paren).length⟩

section
variables {motive : dyck_words → Sort*} (base : motive dyck_words.nil)
  (ind : ∀ (x y : dyck_words), motive x → motive y → motive (x.surround ++ y))
include base ind

@[elab_as_eliminator]
def dyck_words.rec_balance : ∀ x, motive x
| ⟨[], _⟩ := base
| ⟨(x :: xs), p⟩ :=
let X : dyck_words := ⟨(x :: xs), p⟩ in
have hX : X ≠ dyck_words.nil := dec_trivial,
have _ := dyck_words.left_lt hX,
have _ := dyck_words.right_lt hX,
begin
  change motive X, rw ← dyck_words_eq_self hX,
  exact (ind X.left X.right (dyck_words.rec_balance _) (dyck_words.rec_balance _)),
end

@[simp] lemma dyck_words.nil_rec : @dyck_words.rec_balance motive base ind dyck_words.nil = base :=
by { delta dyck_words.nil, simp [dyck_words.rec_balance], }

lemma dyck_words.node_rec' (X : dyck_words) (hX : X ≠ dyck_words.nil) :
  @dyck_words.rec_balance motive base ind X = cast (congr_arg motive $ dyck_words_eq_self hX) (
  ind X.left X.right (dyck_words.rec_balance base ind X.left) (dyck_words.rec_balance base ind X.right)) :=
begin
  induction X using paren.dyck_words.cases_on with xs p, { contradiction, },
  rw dyck_words.rec_balance, refl,
end

private lemma ind_subst {E F E' F' : dyck_words} (hE : E = E') (hF : F = F') :
  ind E F (dyck_words.rec_balance base ind E) (dyck_words.rec_balance base ind F)
  == ind E' F' (dyck_words.rec_balance base ind E') (dyck_words.rec_balance base ind F') :=
by subst_vars

@[simp] lemma dyck_words.node_rec (x y : dyck_words) :
  @dyck_words.rec_balance motive base ind (x.surround ++ y) =
    ind x y (dyck_words.rec_balance base ind x) (dyck_words.rec_balance base ind y) :=
begin
  rw dyck_words.node_rec' base ind (x.surround ++ y),
  { rw cast_eq_iff_heq, exact (ind_subst base ind (dyck_words_left x y) (dyck_words_right x y)), },
  apply_fun (coe : dyck_words → list paren), simp,
end

end

def dyck_words.to_tree (x : dyck_words) : tree unit :=
begin
  induction x using paren.dyck_words.rec_balance with l r ih₁ ih₂,
  { exact tree.nil, },
  { exact ih₁ △ ih₂, },
end

@[simp] lemma dyck_words.nil_to_tree : dyck_words.nil.to_tree = tree.nil :=
by simp [dyck_words.to_tree]

@[simp] lemma dyck_words.node_to_tree (x y : dyck_words) :
  (x.surround ++ y).to_tree = x.to_tree △ y.to_tree :=
by simp [dyck_words.to_tree]

end paren

namespace tree

@[simp] def to_dyck_word : ∀ (x : tree unit), paren.dyck_words
| nil := paren.dyck_words.nil
| (a △ b) := a.to_dyck_word.surround ++ b.to_dyck_word

def equiv_dyck_words : tree unit ≃ paren.dyck_words :=
{ to_fun := to_dyck_word,
  inv_fun := paren.dyck_words.to_tree,
  left_inv := λ x,
begin
  induction x using tree.unit_rec_on with l r ih₁ ih₂, { simp [paren.dyck_words.to_tree], },
  simp [ih₁, ih₂],
end,
  right_inv := λ x,
begin
  induction x using paren.dyck_words.rec_balance with l r ih₁ ih₂,
  { simp, }, { simp [ih₁, ih₂], }
end }

@[simp] lemma equiv_dyck_words_nil : equiv_dyck_words nil = paren.dyck_words.nil := rfl
@[simp] lemma equiv_dyck_words_node (x y : tree unit) : equiv_dyck_words (x △ y) =
  (equiv_dyck_words x).surround ++ (equiv_dyck_words y) := rfl

@[simp] lemma equiv_dyck_words_symm_nil : equiv_dyck_words.symm paren.dyck_words.nil = nil :=
by simp [equiv_dyck_words]

@[simp] lemma equiv_dyck_words_symm_node (x y : paren.dyck_words) :
  equiv_dyck_words.symm (x.surround ++ y) = (equiv_dyck_words.symm x) △ (equiv_dyck_words.symm y) :=
by simp [equiv_dyck_words]

lemma equiv_dyck_words_length (x : tree unit) : 2 * x.num_nodes = (↑(equiv_dyck_words x) : list paren).length :=
begin
  induction x using tree.unit_rec_on with l r ih₁ ih₂,
  { simp, },
  simp [mul_add, ih₁, ih₂], ring,
end

end tree

section algorithms
open paren

/- In this section, we present `foldl` algorithms for decomposing a dyck word.
These are simpler to define (only using `foldl` loops, rather than `init` and `find`)
but more difficult to prove properties about. They are useful when balanced parentheses
are used for defining algorithms. -/

/-- Counts the number of `(` minus `)` plus 1, but returns 0 if 
  there are more `)` than `(`.
  It does this by using an accumulator which gets "stuck" at `0` -/
def sum_parens (l : list paren) : ℕ :=
l.foldl (λ (acc : ℕ) (hd : paren), 
  if acc = 0 then 0
  else if hd = up then acc + 1
  else acc - 1) 1

@[simp] lemma sum_parens_snoc (l : list paren) (b : paren) :
  sum_parens (l ++ [b]) = if sum_parens l = 0 then 0
    else if b = up then sum_parens l + 1 else sum_parens l - 1 := 
by simp [sum_parens]

lemma sum_parens_eq_sum (x : list paren) (h : ∀ pfx, pfx <+: x → 0 ≤ (pfx.map to_int).sum) :
  ((sum_parens x) : ℤ) = (x.map to_int).sum + 1 :=
begin
  induction x using list.reverse_rec_on with l e ih, { refl, },
  simp only [list.is_prefix_snoc_iff] at h,
  specialize ih (λ pfx hpfx, h _ (or.inr hpfx)),
  have : 0 < (sum_parens l),
  { zify, rw ih, specialize h l (or.inr $ list.prefix_refl _), linarith only [h], },
  cases e; simp [ih, this.ne.symm, this],
end


lemma sum_parens_zero_of_pfx_zero {x r} (h : r <+: x) (h' : sum_parens r = 0) :
  sum_parens x = 0 :=
begin
  obtain ⟨x, rfl⟩ := h,
  induction x using list.reverse_rec_on with l e ih,
  { simpa using h', }, { simp [← list.append_assoc, ih], }
end

lemma sum_parens_matching_paren {x} (h : (find_matching_paren x).is_some) :
  sum_parens x = 0 :=
begin
  obtain ⟨r, h⟩ := option.is_some_iff_exists.mp h,
  apply sum_parens_zero_of_pfx_zero (find_matching_paren_is_prefx h),
  have := sum_parens_eq_sum r.init (λ pfx, sum_nonneg_of_pfx_init h),
  rw (find_matching_paren_init h).2 at this, 
  rw ← list.init_append_last' _ (find_matching_paren_last h),
  norm_cast at this,
  simp [this],
end

lemma is_balanced_iff (l : list paren) : sum_parens l = 1 ↔ are_heights_nonneg l :=
begin
  split,
  { rw are_heights_nonneg, contrapose!,
    intros h₁ h₂,
    suffices : _, { refine h₁ this _, zify at h₂, rw sum_parens_eq_sum _ this at h₂, simpa using h₂, },
    contrapose! h₂,
    rw sum_parens_matching_paren, { trivial, },
    erw list.find_is_some, simpa using h₂, },
  { intro h, rcases l with (_|⟨(hd|hd), tl⟩), { refl, }, 
    { have := sum_parens_eq_sum _ h.1, rw h.2 at this, simpa, },
    exfalso, exact not_are_heights_nonnneg_down_cons _ h, },
end

def left_alg_foldl (acc : list paren) (e : paren) : list paren :=
  if ¬acc.empty ∧ are_heights_nonneg acc then acc
  else acc ++ [e]

lemma left_alg_spec {x : list paren} (hx : ∀ pfx, pfx <+: x.init → 0 ≤ (pfx.map paren.to_int).sum) :
  (up :: x).foldl left_alg_foldl [] = up :: x :=
begin
  induction x using list.reverse_rec_on with l e ih, { simp [left_alg_foldl], },
  rw list.snoc_init at hx,
  specialize ih (λ pfx h, hx _ (h.trans l.init_prefix)),
  rw [← list.cons_append, list.foldl_append, ih],
  have : ¬are_heights_nonneg (up :: l),
  { rintro ⟨_, h⟩, specialize hx _ (list.prefix_refl _), simp at h, linarith only [hx, h], }, 
  simpa [left_alg_foldl],
end

lemma left_alg_spec' {x : dyck_words} {y : list paren} :
  ((↑x.surround : list paren) ++ y).foldl left_alg_foldl [] = 
    (↑x.surround : list paren) :=
begin
  rw [list.foldl_append, dyck_words.surround_val, list.cons_append, left_alg_spec, list.foldl_fixed'],
  { intro b, rw [left_alg_foldl, if_pos], simpa using x.surround.prop, },
  { simpa using x.prop.1, },
end

def left_dyck_word (x : list paren) : list paren :=
if x.empty then [] else (x.foldl left_alg_foldl []).tail.init

@[simp] lemma left_dyck_word_spec (x : dyck_words) : left_dyck_word ↑x = ↑x.left :=
begin
  induction x using paren.dyck_words.rec_balance with l r _ _, { simp [left_dyck_word, left_alg_foldl], },
  rw [left_dyck_word, dyck_words.append_val, left_alg_spec'],
  simp,
end

def right_dyck_word (x : list paren) : list paren := x.drop ((left_dyck_word x).length + 2)

@[simp] lemma right_dyck_word_spec (x : dyck_words) : right_dyck_word ↑x = ↑x.right :=
begin
  induction x using paren.dyck_words.rec_balance with l r _ _, { simp [right_dyck_word], },
  rw [right_dyck_word, left_dyck_word_spec], simp [list.drop_append],
end

end algorithms
