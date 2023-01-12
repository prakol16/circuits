import polytime.lemmas

variables {α β γ : Type} [tencodable α] [tencodable β] [tencodable γ]
open_locale complexity_class

@[simp] def zip {α β : Type*} : list α → list β → list (α × β)
| (x :: xs) (y :: ys) := (x, y) :: zip xs ys
| _ _ := []

theorem zip_eq_stack_rec (l₁ : list α) (l₂ : list β) :
  zip l₁ l₂ = l₁.stack_rec (λ l₂' : list β, []) (λ x xs l₂', l₂'.tail)
    (λ ih x xs l₂', @list.cases_on _ (λ _, list (α × β)) l₂' [] (λ y ys, (x, y) :: ih)) l₂ :=
by induction l₁ generalizing l₂; cases l₂; simp [*]

example : (@zip α β) ∈ₑ PTIME :=
begin
  complexity using λ l₁ l₂, l₁.stack_rec (λ l₂' : list β, []) (λ x xs l₂', l₂'.tail)
    (λ ih x xs l₂', @list.cases_on _ (λ _, list (α × β)) l₂' [] (λ y ys, (x, y) :: ih)) l₂,
  induction l₁ generalizing l₂; cases l₂; simp [*],
end

