import complexity_class.stack_rec
import polytime.basic
import polytime.stack_rec_size

open tree (stack_step iterator_stack stack_step_polysize)
open tencodable function polysize

namespace polytime

open_locale complexity_class

variables {α β γ δ : Type} [tencodable α] [tencodable β] [tencodable γ] [tencodable δ]

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
  { use 0, simp, },
  induction x using tree.unit_rec_on with l r ih₁ ih₂ generalizing y; cases y; simp [*],
end

@[complexity] lemma eq : (@eq α) ∈ₚ PTIME :=
by { have := tree_eq, complexity using (λ x y, encode x = encode y), simp, }

@[complexity] lemma tree_cmp : (@tree.cmp unit _ _) ∈ₑ PTIME :=
begin
  complexity using λ x y,
    x.stack_rec (λ y', if y' = tree.nil then ordering.eq else ordering.lt)
      (λ _ _ y', y'.left) (λ _ _ y', y'.right)
      (λ c₁ c₂ _ _ y', if y' = tree.nil then ordering.gt else c₁.or_else c₂) y,
  { use 0, simp, },
  induction x using tree.unit_rec_on with l r ih₁ ih₂ generalizing y; rcases y with _|⟨⟨⟩, _, _⟩; simp [*, tree.cmp, ordering.or_else],
end

@[complexity] lemma tree_lt : ((<) : tree unit → tree unit → Prop) ∈ₚ PTIME :=
by { complexity using λ x y, x.cmp y = ordering.lt, rw tree.tree_lt_def, }

@[complexity] lemma tree_le : ((≤) : tree unit → tree unit → Prop) ∈ₚ PTIME :=
by { complexity using λ x y, ¬(y < x), simp, }

end stack_rec

end polytime
