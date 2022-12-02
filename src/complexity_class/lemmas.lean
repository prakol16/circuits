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

protected lemma mem_iff_comp_encode {f : α → β} :
  f ∈ₑ C ↔ (λ x, encode (f x)) ∈ₑ C := iff.rfl

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
by { classical, simp [← mem_iff_mem_pred'], complexity, }

/-- Complexity classes are closed under complementation -/
@[complexity] protected lemma not {P : α → Prop} (h : P ∈ₚ C) : C.mem_pred (λ x, ¬(P x)) :=
by { classical, simp [← mem_iff_mem_pred'], complexity, }

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

@[complexity] lemma tree_cases {f : α → tree unit} {g : α → β}
  {h : α → unit → tree unit → tree unit → β} (hf : f ∈ₑ C) (hg : g ∈ₑ C) (hh : h ∈ₑ C) :
  @complexity_class.mem α β (α → β) _ _ _ (λ x, @tree.cases_on unit (λ _, β) (f x) (g x) (h x)) C :=
begin
  complexity using (λ x, if f x = tree.nil then g x else h x () (f x).left (f x).right),
  cases f x, { simp, }, cases ᾰ, simp,
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
by { classical, simp [← mem_iff_mem_pred'], complexity, }

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

lemma prod_decode (h₁ : decode α ∈ₑ C) (h₂ : decode β ∈ₑ C) : decode (α × β) ∈ₑ C :=
by { dsimp [decode], complexity, }

end complexity_class

