import complexity_class.lemmas
import stack_rec

variables (C : complexity_class) {α β γ : Type} [tencodable α] [tencodable β] [tencodable γ]
  {base : γ → α → β} {pre₁ pre₂ : γ → tree unit → tree unit → α → α}
  {post : γ → β → β → tree unit → tree unit → α → β}

open_locale complexity_class

lemma complexity_class.stack_iterate {start : γ → list (tree.iterator_stack α β)}
  (hb : base ∈ₑ C) (hp₁ : pre₁ ∈ₑ C) (hp₂ : pre₂ ∈ₑ C)
  (hp : post ∈ₑ C) (hs : start ∈ₑ C) :
   C.mem (λ x : γ, tree.stack_step (base x) (pre₁ x) (pre₂ x) (post x) (start x)) :=
by { delta tree.stack_step, clean_target, complexity, }


