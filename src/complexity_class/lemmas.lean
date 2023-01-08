import complexity_class.tactic

open tencodable (encode decode)
open function

variables {C : complexity_class} {α β γ δ ε : Type} [tencodable α]
  [tencodable β] [tencodable γ] [tencodable δ] [tencodable ε]

namespace complexity_class
open_locale complexity_class
open_locale tree

@[complexity] lemma prod_mk : @prod.mk α β ∈ₑ C := C.id'
@[complexity] lemma cons : @list.cons α ∈ₑ C := C.id'
@[complexity] protected lemma encode : @encode α _ ∈ₑ C := C.id'
@[complexity] lemma sigma_mk : @complexity_class.mem _ _ (α → β → (Σ _ : α, β)) _ _ _ sigma.mk C := C.id'

lemma mem_iff_comp_encode {f : α → β} :
  f ∈ₑ C ↔ (λ x, encode (f x)) ∈ₑ C := iff.rfl

lemma mem_iff_comp_encode' {C : complexity_class} {β γ : Type} [tencodable γ] {f : β → α} {finv : α → option β} {linv : ∀ b, finv (f b) = some b} 
  {g : γ → β} : by haveI : tencodable β := tencodable.of_left_injection f finv linv; exact 
  g ∈ₑ C ↔ (λ x, f (g x)) ∈ₑ C := iff.rfl

@[complexity] lemma tree_left : @tree.left unit ∈ₑ C :=
⟨_, C.left, λ _, rfl⟩

@[complexity] lemma tree_right : @tree.right unit ∈ₑ C :=
⟨_, C.right, λ _, rfl⟩

@[complexity] lemma tree_node : (tree.node ()) ∈ₑ C :=
⟨_, C.id, λ _, rfl⟩

@[complexity] lemma unit_rec {f : α → unit} {g : α → β} (hg : g ∈ₑ C) :
  @complexity_class.mem _ _ (α → β) _ _ _ (λ x : α, @punit.rec (λ _, β) (g x) (f x)) C := 
by { convert hg, ext x, cases f x, refl, }

private lemma eq_nil_aux : (=@tree.nil unit) ∈ₚ C :=
⟨_, C.ite' C.id (C.prop_const $ encode tt)
  (C.prop_const $ encode ff), λ x, by cases x; simp [has_uncurry.uncurry]⟩

@[complexity] lemma coe_sort : (λ b : bool, (b : Prop)) ∈ₚ C :=
⟨_, C.id, λ _, by simp [has_uncurry.uncurry]⟩

@[complexity] lemma to_bool {P : α → Prop} [decidable_pred P] (hP : P ∈ₚ C) :
  C.mem (λ x, to_bool (P x)) :=
by { convert hP, ext, congr, }

@[complexity] protected lemma band : C.mem (&&) :=
by { complexity using (λ (b₁ b₂ : bool), if b₁ then b₂ else ff), cases b₁; simp, }

@[complexity] protected lemma bnot : C.mem bnot :=
by { complexity using (λ b, if b then ff else tt), cases b; refl, }

/-- Complexity classes are closed under intersection -/
@[complexity] protected lemma and {P₁ P₂ : α → Prop} (h₁ : P₁ ∈ₚ C) (h₂ : P₂ ∈ₚ C) :
  (λ x, (P₁ x) ∧ (P₂ x)) ∈ₚ C :=
by { classical, simp [← mem_iff_mem_pred], complexity, }

/-- Complexity classes are closed under complementation -/
@[complexity] protected lemma not {P : α → Prop} (h : P ∈ₚ C) : C.mem_pred (λ x, ¬(P x)) :=
by { classical, simp [← mem_iff_mem_pred], complexity, }

@[complexity] lemma eq_const_aux : ∀ (x : tree unit), (=x) ∈ₚ C
| tree.nil := eq_nil_aux
| (a △ b) :=
begin
  have := (eq_const_aux a).comp tree_left, have := (eq_const_aux b).comp tree_right, have := @eq_nil_aux C,
  complexity using (λ y, ¬(y = tree.nil) ∧ y.left = a ∧ y.right = b),
  cases y; simp,
end

@[complexity] lemma eq_const {f : α → β} (hf : f ∈ₑ C) (y : β) :
  C.mem_pred (λ x, (f x) = y) :=
by simpa using (eq_const_aux (encode y)).comp hf

@[complexity] lemma list_empty : @list.empty α ∈ₑ C :=
by { classical, complexity using λ l, l = [], cases l; simp, }

@[complexity] lemma option_is_none : @option.is_none α ∈ₑ C :=
by { classical, complexity using λ x, x = none, cases x; simp, }

@[complexity] lemma option_is_some : @option.is_some α ∈ₑ C :=
by { complexity using λ x, !x.is_none, cases x; simp, }

@[complexity] lemma tree_cases {f : α → tree unit} {g : α → β}
  {h : α → unit → tree unit → tree unit → β} (hf : f ∈ₑ C) (hg : g ∈ₑ C) (hh : h ∈ₑ C) :
  @complexity_class.mem α β (α → β) _ _ _ (λ x, @tree.cases_on unit (λ _, β) (f x) (g x) (h x)) C :=
begin
  complexity using (λ x, if f x = tree.nil then g x else h x () (f x).left (f x).right),
  rcases f x with (_|⟨⟨⟩, _, _⟩); simp,
end

lemma of_fin_cases [nonempty γ] (S : finset α)
  {f : α → β → γ} (hf : ∀ {x}, x ∈ S → f x ∈ₑ C) :
  ∃ f' : α → β → γ, f' ∈ₑ C ∧ ∀ {x}, x ∈ S → f x = f' x :=
begin
  classical, inhabit γ,
  induction S using finset.induction with x xs x_nmem ih,
  { refine ⟨λ _ _, default, by complexity, _⟩, simp, },
  rcases ih (λ _ h, hf (finset.mem_insert.mpr (or.inr h))) with ⟨f', pf, hf'⟩,
  set g := f x, have : g ∈ₑ C := by { apply hf, simp, },
  refine ⟨λ x' y, if x' = x then g y else f' x' y, by complexity, _⟩,
  intro x', split_ifs with H, { simp [H], }, { simpa [H] using hf', },
end

@[complexity] lemma of_to_empty [H : is_empty β] (f : α → β) : f ∈ₑ C :=
⟨_, C.nil, λ x, H.elim' (f x)⟩

/-- A function on a `fintype` is in the complexity class iff each function is (i.e. we can always do
  a finite amount of casework) -/
lemma of_from_fintype [fintype α] {f : α → β → γ} (hf : ∀ x, f x ∈ₑ C) : f ∈ₑ C :=
begin
  casesI is_empty_or_nonempty γ, 
  { apply of_to_empty, },
  obtain ⟨f', pf, hf'⟩ := of_fin_cases (@finset.univ α _) (λ x _, hf x),
  convert pf, apply funext, simpa using @hf',
end

lemma iff_fintype [fintype α] {f : α → β → γ} :
  f ∈ₑ C ↔ ∀ x, f x ∈ₑ C :=
⟨λ h x, h.comp₂ (C.const x) C.id', of_from_fintype⟩

lemma of_from_fintype' [fintype α] (f : α → β) : f ∈ₑ C :=
let H : C.mem (λ x (_ : unit), f x) := of_from_fintype (λ x, C.const _)
 in H.comp₂ C.id' (C.const ())

@[complexity] protected lemma bor : bor ∈ₑ C := of_from_fintype' _

/-- Complexity classes are closed under union -/
@[primrec] protected lemma or {P Q : α → Prop} (hP : P ∈ₚ C) (hQ : Q ∈ₚ C) :
  C.mem_pred (λ x, (P x) ∨ (Q x)) :=
by { classical, simp [← mem_iff_mem_pred], complexity, }

section option

@[complexity] lemma option_elim {f : α → option β} {g : α → γ} {h : α → β → γ} :
  f ∈ₑ C → g ∈ₑ C → h ∈ₑ C → C.mem (λ x, (f x).elim (g x) (h x)) :=
begin
  rintros ⟨f', pf, hf⟩ ⟨g', pg, hg⟩ ⟨h', ph, hh⟩, replace hh := λ x₁ x₂, hh (x₁, x₂),
  refine ⟨λ x, if f' x = tree.nil then g' x else h' (x △ (f' x).right), _, _⟩,
  { complexity, },
  intro x,
  simp only [hf, hg], dsimp [has_uncurry.uncurry],
  cases f x,
  { simp [encode], },
  { simpa [encode] using hh _ _, },
end

@[complexity] lemma option_rec {f : α → option β} {g : α → γ} {h : α → β → γ} (hf : f ∈ₑ C)
  (hg : g ∈ₑ C) (hh : h ∈ₑ C) :
  @complexity_class.mem α γ (α → γ) _ _ _ (λ x : α, @option.rec β (λ _, γ) (g x) (h x) (f x)) C :=
by { convert option_elim hf hg hh, ext x, cases f x; refl, }

@[complexity] protected lemma some : @option.some α ∈ₑ C :=
⟨_, C.pair C.nil C.id, λ _, rfl⟩

@[complexity] lemma succ : nat.succ ∈ₑ C := complexity_class.some 

lemma of_some {f : α → β} : f ∈ₑ C ↔ C.mem (λ x, some (f x)) :=
⟨λ hf, by complexity, λ ⟨f', pf, hf⟩, ⟨_, C.comp C.right pf, λ _, by { simp [hf], refl, }⟩⟩

@[complexity] lemma option_bind {f : α → option β} {g : α → β → option γ} (hf : f ∈ₑ C)
  (hg : g ∈ₑ C) : C.mem (λ x, (f x).bind (g x)) :=
by { delta option.bind, clean_target, complexity, }

@[complexity] lemma option_map {f : α → option β} {g : α → β → γ} (hf : f ∈ₑ C) (hg : g ∈ₑ C) :
  C.mem (λ x, (f x).map (g x)) :=
by { delta option.map, complexity, }

def mem' {γ : Type} [has_uncurry γ α β] (f : γ) (C : complexity_class) : Prop :=
C.prop (λ x, encode $ (decode α x).map ↿f)

localized "infix ` ∈ₛ `:50 := complexity_class.mem'" in complexity_class

lemma mem_of_mem' {γ : Type} [has_uncurry γ α β] {f : γ} {C : complexity_class}
  (hf : f ∈ₛ C) : f ∈ₑ C := ⟨_, C.comp C.right hf, by simp [encode]⟩

lemma mem'_iff_mem_decode {γ : Type} [has_uncurry γ α β] {f : γ} {C : complexity_class} (h : decode α ∈ₑ C) :
  f ∈ₛ C ↔ f ∈ₑ C := ⟨mem_of_mem', λ H, by { dsimp only [mem'], complexity, }⟩ 

protected lemma decode : decode (tree unit) ∈ₑ C := complexity_class.some 

lemma option_decode (h : decode α ∈ₑ C) : decode (option α) ∈ₑ C :=
by { simp only [decode], delta tencodable.to_option, clean_target, complexity, }

end option

section sum

@[complexity] lemma sum_elim {f : α → β ⊕ γ} {g : α → β → δ} {h : α → γ → δ} :
  f ∈ₑ C → g ∈ₑ C → h ∈ₑ C → C.mem (λ x, (f x).elim (g x) (h x)) :=
begin
  rintros ⟨f', pf, hf⟩ ⟨g', pg, hg⟩ ⟨h', ph, hh⟩, simp only [prod.forall] at hg hh,
  refine ⟨λ x, if (f' x).left = tree.nil then g' (x △ (f' x).right)
               else h' (x △ (f' x).right), _, _⟩,
  { complexity, },
  intro x,
  simp only [hf, encode, tencodable.of_sum, tencodable.to_sum, has_uncurry.uncurry, id_def],
  cases f x,
  { simpa using hg _ _, },
  { simpa using hh _ _, }
end

@[complexity] lemma sum_inl : @sum.inl α β ∈ₑ C :=
⟨_, C.pair C.nil C.id, by simp [encode, has_uncurry.uncurry]⟩

@[complexity] lemma sum_inr : @sum.inr α β ∈ₑ C :=
⟨_, C.pair (C.prop_const tencodable.non_nil) C.id, by simp [encode, has_uncurry.uncurry]⟩

@[complexity] lemma sum_rec {f : α → β ⊕ γ} {g : α → β → δ} {h : α → γ → δ} (hf : f ∈ₑ C)
  (hg : g ∈ₑ C) (hh : h ∈ₑ C) :
  @complexity_class.mem α δ (α → δ) _ _ _ (λ x, @sum.rec β γ (λ _, δ) (g x) (h x) (f x)) C := sum_elim hf hg hh

-- TODO: some kind of derive handler for these things which are easy
@[complexity] lemma sum_get_right : @sum.get_right α β ∈ₑ C :=
by { delta sum.get_right, clean_target, complexity, }

lemma sum_decode (h₁ : decode α ∈ₑ C) (h₂ : decode β ∈ₑ C) : decode (α ⊕ β) ∈ₑ C :=
by { dsimp [decode], delta tencodable.to_sum, complexity, }

end sum

section prod

lemma prod_decode (h₁ : decode α ∈ₑ C) (h₂ : decode β ∈ₑ C) : decode (α × β) ∈ₑ C :=
by { dsimp [decode], complexity, }

@[complexity] lemma prod_rec {f : α → β × γ} {g : α → β → γ → δ} (hf : f ∈ₑ C) (hg : g ∈ₑ C) :
  @complexity_class.mem α δ (α → δ) _ _ _ (λ x, @prod.rec β γ (λ _, δ) (g x) (f x)) C :=
by { complexity using (λ x, g x (f x).1 (f x).2), cases f x; refl, }

end prod

section ordering

@[complexity] lemma ordering_swap : ordering.swap ∈ₑ C := of_from_fintype' _

@[complexity] lemma ordering_or_else : ordering.or_else ∈ₑ C := of_from_fintype' _

end ordering

section list

@[complexity] lemma list_cases {f : α → list β} {g : α → γ} {h : α → β → list β → γ} :
  f ∈ₑ C → g ∈ₑ C → h ∈ₑ C →
  @complexity_class.mem α γ (α → γ) _ _ _ (λ x, @list.cases_on β (λ _, γ) (f x) (g x) (h x)) C :=
begin
  rintros ⟨f', pf, hf⟩ ⟨g', pg, hg⟩ ⟨h', ph, hh⟩, replace hh := λ x₁ x₂ x₃, hh (x₁, x₂, x₃),
  use λ x, if f' x = tree.nil then g' x else h' (encode (x, (f' x).left, (f' x).right)),
  split, { complexity, },
  intro x, simp only [hf, hg], dsimp [has_uncurry.uncurry, id],
  cases f x, { simp [encode], }, { simpa [encode] using hh _ _ _, },
end

@[complexity] lemma head' : (@list.head' α) ∈ₑ C :=
by { delta list.head', clean_target, complexity, }

@[complexity] lemma head [inhabited α] : (@list.head α _) ∈ₑ C :=
by { delta list.head, clean_target, complexity, }

@[complexity] lemma tail : (@list.tail α) ∈ₑ C :=
by { delta list.tail, clean_target, complexity, }

@[complexity] lemma pred : nat.pred ∈ₑ C :=
⟨_, C.right, λ n, by cases n; simp [has_uncurry.uncurry, encode]⟩

@[complexity] protected lemma equiv_list : ⇑tencodable.equiv_list ∈ₑ C :=
⟨_, C.id, λ x, by simp [encode, has_uncurry.uncurry]⟩ 

@[complexity] protected lemma equiv_list_symm : ⇑tencodable.equiv_list.symm ∈ₑ C :=
⟨_, C.id, λ x, by simp [encode, has_uncurry.uncurry]⟩

lemma const_list_nth (n : ℕ) : (λ l : list α, l.nth n) ∈ₑ C :=
begin
  induction n with n ih, { convert head', ext x : 1, cases x; refl, },
  have : (λ l : list α, l.tail.nth n) ∈ₑ C := ih.comp tail,
  complexity using λ l, if l.empty then none else l.tail.nth n,
  cases l; simp,
end

end list

section equiv


lemma encode_of_left_injection  {β : Type} {f : β → α} {finv : α → option β} {linv : ∀ b, finv (f b) = some b} :
  by haveI : tencodable β := tencodable.of_left_injection f finv linv; exact f ∈ₑ C :=
⟨_, C.id, λ x, rfl⟩

lemma decode_of_left_injection  {β : Type} {f : β → α} {finv : α → option β} {linv : ∀ b, finv (f b) = some b} 
  (hd : decode α ∈ₑ C) (hf : by haveI : tencodable β := tencodable.of_left_injection f finv linv; exact finv ∈ₑ C) :
  by haveI : tencodable β := tencodable.of_left_injection f finv linv; exact decode β ∈ₑ C :=
by { letI : tencodable β := tencodable.of_left_injection f finv linv, refine option_bind hd _, complexity, }

lemma encode_of_equiv {C : complexity_class} {β : Type} {e : β ≃ α} :
  by haveI : tencodable β := tencodable.of_equiv _ e; exact ⇑e ∈ₑ C := encode_of_left_injection

lemma decode_of_equiv {C : complexity_class} {β : Type} {e : β ≃ α} :
  by haveI : tencodable β := tencodable.of_equiv _ e; exact ⇑e.symm ∈ₑ C :=
⟨_, C.id, λ x, congr_arg encode (e.apply_symm_apply x).symm⟩

lemma decodable_of_equiv {C : complexity_class} {β : Type} {e : β ≃ α} (hd : decode α ∈ₑ C) :
  by haveI : tencodable β := tencodable.of_equiv _ e; exact decode β ∈ₑ C :=
by letI : tencodable β := tencodable.of_equiv _ e; exact decode_of_left_injection hd (mem.comp complexity_class.some decode_of_equiv)

end equiv

section subtype

@[complexity] lemma subtype_coe {P : α → Prop} [decidable_pred P] : (coe : {x // P x} → α) ∈ₑ C :=
encode_of_left_injection

@[complexity] lemma subtype_val {P : α → Prop} [decidable_pred P] : (subtype.val : {x // P x} → α) ∈ₑ C :=
subtype_coe

@[complexity] lemma subtype_rec {P : α → Prop} [decidable_pred P]
  {f : β → {x // P x}} {g : β → ∀ x, P x → γ} :
  f ∈ₑ C → (λ (a : β) (b : {x // P x}), g a b b.prop) ∈ₑ C →
  @complexity_class.mem _ _ (β → γ) _ _ _ (λ x, @subtype.rec _ _ (λ _, γ) (g x) (f x)) C
| ⟨f', pf, hf⟩ ⟨g', pg, hg⟩ := ⟨λ x, g' (x △ (f' x)), by complexity, λ x, begin
  dsimp [has_uncurry.uncurry] at hg hf ⊢,
  simp [tencodable.encode_prod] at hg,
  simp [hf, hg], cases f x, refl,
end⟩

@[complexity] lemma of_subtype_coe {P : α → Prop} [decidable_pred P] {f : β → {x // P x}} :
  f ∈ₑ C ↔ (λ x, (f x : α)) ∈ₑ C := iff.rfl

@[complexity] lemma subtype_mk {f : α → β} {P : β → Prop} [decidable_pred P] (hP : ∀ x, P (f x))
  (hf : f ∈ₑ C) : (λ x, subtype.mk (f x) (hP x)) ∈ₑ C := hf

@[complexity] protected lemma dite {P : α → Prop} [decidable_pred P] {f : ∀ (x : α), P x → β}
  {g : ∀ (x : α), ¬P x → β} : P ∈ₚ C → (λ x : {a // P a}, f x x.prop) ∈ₑ C →
  (λ x : {a // ¬P a}, g x x.prop) ∈ₑ C → (λ x, if H : P x then f x H else g x H) ∈ₑ C
| ⟨P', pP, hP⟩ ⟨f', pf, hf⟩ ⟨g', pg, hg⟩ :=
⟨λ x, if P' x = encode tt then f' x else g' x, by complexity,
begin
  intro x,
  simp only [hP, has_uncurry.uncurry, tencodable.encode_inj], dsimp, simp only [to_bool_iff],
  split_ifs with H,
  { simp [tencodable.subtype_encode] at hf, simp [hf, H], refl, },
  { simp [tencodable.subtype_encode] at hg, simp [hg, H], refl, }
end⟩

lemma subtype_decode {P : α → Prop} [decidable_pred P] (hd : decode α ∈ₑ C)
  (hP : P ∈ₚ C) : decode {x // P x} ∈ₑ C :=
decode_of_left_injection hd (by complexity)

@[complexity] lemma fin_mk {n} {f : α → ℕ} (P : ∀ x, f x < n) (hf : f ∈ₑ C) :
  (λ x, (⟨f x, P x⟩ : fin n)) ∈ₑ C := hf

@[complexity] lemma fin_coe {n} : (coe : fin n → ℕ) ∈ₑ C :=
⟨_, C.id, λ _, rfl⟩

@[complexity] lemma fin_val {n} : (fin.val : fin n → ℕ) ∈ₑ C := fin_coe

@[complexity] lemma fin_rec {n : ℕ} {f : α → fin n} {g : α → ∀ (x : ℕ), x < n → β} :
  f ∈ₑ C → (λ (a : α) (b : {x // x < n}), g a b b.prop) ∈ₑ C →
  @complexity_class.mem _ _ (α → β) _ _ _ (λ x, @fin.rec n (λ _, β) (g x) (f x)) C
| ⟨f', pf, hf⟩ ⟨g', pg, hg⟩ := ⟨λ x, g' (x △ (f' x)), by complexity, λ x, begin
  dsimp [has_uncurry.uncurry] at hg hf ⊢,
  cases H : f x with v hv, specialize hg (x, ⟨v, hv⟩),
  simp [tencodable.encode_prod] at hg,
  simpa [hf, H] using hg,
end⟩

@[complexity] lemma vector_to_list {n} : (vector.to_list : vector α n → list α) ∈ₑ C :=
subtype_coe

@[complexity] lemma vector_head {n} : (@vector.head α n) ∈ₑ C :=
by { rw of_some, simp_rw ← vector.head'_to_list, complexity, }

@[complexity] lemma vector_tail {n} : (@vector.tail α n) ∈ₑ C :=
by { complexity using λ l, subtype.mk l.to_list.tail (by simp), rcases l with ⟨_|_, _⟩; refl, }

@[complexity] lemma vector_cons {n} : (@vector.cons α n) ∈ₑ C :=
by { complexity using λ x v, ⟨x :: v.to_list, by simp⟩, cases v, refl, }

@[complexity] lemma vector_nth {n} : (@vector.nth α n) ∈ₑ C :=
begin
  rw [mem.swap_args₂, iff_fintype],
  intro i, rw of_some,
  convert (const_list_nth i).comp vector_to_list,
  ext x : 1, simp [flip, vector.nth_eq_nth_le,  list.some_nth_le_eq],
end

@[complexity] lemma of_fn {n : ℕ} {f : fin n → α → β} (hf : ∀ i, (f i) ∈ₑ C) :
  (λ x, vector.of_fn (λ i, f i x)) ∈ₑ C :=
begin
  induction n with n ih, { exact C.const vector.nil, },
  exact vector_cons.comp₂ (hf 0) (ih $ λ i, hf i.succ),
end

end subtype

section setoid
variables [h : setoid α] {out : quotient h → α} {hout : function.left_inverse quotient.mk out}

include h out hout C

lemma setoid_out : by haveI : tencodable (quotient h) := setoid.tencodable h out hout; exact out ∈ₑ C :=
⟨_, C.id, λ x, rfl⟩

lemma decodable_of_quotient_mk (hd : decode α ∈ₑ C) (hq : by haveI : tencodable (quotient h) := setoid.tencodable h out hout; exact @quotient.mk _ h ∈ₑ C) :
  by haveI : tencodable (quotient h) := setoid.tencodable h out hout; exact (decode (quotient h)) ∈ₑ C :=
by { letI : tencodable (quotient h) := setoid.tencodable h out hout, refine decode_of_left_injection hd (mem.comp complexity_class.some hq), }

lemma quotient_lift {f : α → β} {pf : ∀ (a b : α), a ≈ b → f a = f b}
  (hf : f ∈ₑ C) : by haveI : tencodable (quotient h) := setoid.tencodable h out hout; exact
  (quotient.lift f pf) ∈ₑ C :=
begin
  letI : tencodable (quotient h) := setoid.tencodable h out hout,
  convert hf.comp setoid_out, ext x,
  refine quotient.induction_on x (λ x, pf _ _ (quotient.exact _)),
  rw hout,
end
 
end setoid

section multiset

@[complexity] lemma multiset_sort : multiset.sort (@tencodable.lift_le α _) ∈ₑ C := setoid_out

end multiset

section sigma

@[complexity] lemma sigma_fst {β : α → Type} [∀ i, tencodable (β i)] :
  (@sigma.fst α β) ∈ₑ C :=
⟨_, C.left, λ x, rfl⟩

@[complexity] lemma sigma_snd : @complexity_class.mem _ _ ((Σ _ : α, β) → β) _ _ _ sigma.snd C :=
⟨_, C.right, λ x, rfl⟩

end sigma

section finmap

@[complexity] lemma finmap_entries [decidable_eq α] : (@finmap.entries α (λ _, β)) ∈ₑ C := C.id'

@[complexity] lemma finmap_decode [decidable_eq α] (hd : decode (multiset (Σ _ : α, β)) ∈ₑ C) 
  (H : @multiset.nodupkeys α (λ _, β) ∈ₚ C) :
  decode (@finmap α (λ _, β)) ∈ₑ C :=
decodable_of_equiv $ subtype_decode hd H

end finmap

end complexity_class

