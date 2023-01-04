import data.finset.basic
import data.polynomial.basic


universes u v w

structure precircuit (U : Type u) (V : Type v) : Type (max u v) :=
(deps : V → list (U ⊕ V))
(wf : well_founded (λ v₁ v₂, sum.inr v₁ ∈ deps v₂))

structure circuit (α : Type w) (U : Type u) (V : Type v)
  extends precircuit U V : Type (max u v w)  :=
(val : V → list α → α)

variables {α U V W X : Type*}

@[simp] def precircuit.deps' (c : precircuit U V) : U ⊕ V → list (U ⊕ V)
| (sum.inl u) := []
| (sum.inr v) := c.deps v

private lemma precircuit.inl_acc (c : precircuit U V) (u : U) :
  acc (λ u₁ u₂, u₁ ∈ c.deps' u₂) (sum.inl u) :=
acc.intro _ (λ y hy, (list.not_mem_nil _ hy).elim) 

lemma precircuit.wf' (c : precircuit U V) :
  well_founded (λ u₁ u₂, u₁ ∈ c.deps' u₂) :=
well_founded.intro (λ a, begin
  cases a, { exact c.inl_acc a, },
  apply c.wf.induction a, intros x ih, apply acc.intro,
  rintros (y|y) hy,
  { exact c.inl_acc y, },
  { exact ih _ hy, },
end)

def eval_aux (c : circuit α U V) (input : U → α) :
  ∀ (x : U ⊕ V), (∀ y ∈ c.deps' x, α) → α
| (sum.inl u) _ := input u
| (sum.inr v) h := c.val v ((c.deps v).attach.map (λ y, h y y.prop))

def circuit.eval (c : circuit α U V) (input : U → α) (v : U ⊕ V) : α :=
c.wf'.fix (eval_aux c input) v

lemma circuit.eval_eq (c : circuit α U V) (input : U → α) (v : U ⊕ V) :
  c.eval input v = eval_aux c input v (λ y _, c.eval input y) := c.wf'.fix_eq _ _

@[simp] lemma circuit.eval_input (c : circuit α U V) (input : U → α) (u : U) :
  c.eval input (sum.inl u) = input u :=
by rw [circuit.eval_eq, eval_aux]

lemma circuit.eval_output (c : circuit α U V) (input : U → α) (v : V) :
  c.eval input (sum.inr v) = c.val v ((c.deps v).map (c.eval input)) :=
by rw [circuit.eval_eq, eval_aux, list.attach_map_coe']

def precircuit.depth (c : precircuit U V) (x : U ⊕ V) : ℕ :=
circuit.eval ⟨c, λ _ ls, ls.to_finset.sup id + 1⟩ (λ _, 0) x

def comp_dep (deps₁ : V → list (U ⊕ V)) (deps₂ : X → list (W ⊕ X)) (f : W → U ⊕ V) : V ⊕ X → list (U ⊕ V ⊕ X)
| (sum.inl v) := (deps₁ v).map (λ x, (equiv.sum_assoc U V X) (sum.inl x))
| (sum.inr x) := (deps₂ x).map (λ wx, (equiv.sum_assoc U V X) (wx.map f id))

@[simp] lemma inr_inr_mem_comp_dep_inr {deps₁ : V → list (U ⊕ V)} {deps₂ : X → list (W ⊕ X)} {f : W → U ⊕ V}
  {x₁ x₂ : X} : (sum.inr $ sum.inr x₁) ∈ comp_dep deps₁ deps₂ f (sum.inr x₂) ↔ sum.inr x₁ ∈ deps₂ x₂ :=
by { simp [comp_dep], intro x, cases f x; simp, }

@[simps]
def precircuit.comp (c₁ : precircuit U V) (c₂ : precircuit W X) (f : W → U ⊕ V) :
  precircuit U (V ⊕ X) :=
{ deps := λ x, comp_dep c₁.deps c₂.deps f x,
  wf := well_founded.intro (λ a, begin
    have : ∀ v, acc (λ v₁ v₂ : V ⊕ X, sum.inr v₁ ∈ comp_dep c₁.deps c₂.deps f v₂) (sum.inl v),
    { intro v,
      apply c₁.wf.induction v, intros x ih, apply acc.intro,
      simpa [comp_dep] using ih, },
    cases a, { exact this a, },
    apply c₂.wf.induction a, intros x ih, apply acc.intro,
    intros y hy,
    cases y, { exact this y, },
    rw inr_inr_mem_comp_dep_inr at hy,
    exact ih _ hy,
  end) }

@[simps] def circuit.comp (c₁ : circuit α U V) (c₂ : circuit α W X) (f : W → U ⊕ V) : circuit α U (V ⊕ X) :=
{ val := λ x, x.elim c₁.val c₂.val,
  ..(precircuit.comp c₁.to_precircuit c₂.to_precircuit f) }

@[simp] lemma circuit.comp_eval_inr_inl (c₁ : circuit α U V) (c₂ : circuit α W X) (f : W → U ⊕ V) (input : U → α)
  (v : V) : (c₁.comp c₂ f).eval input (sum.inr $ sum.inl v) = c₁.eval input (sum.inr v) :=
begin
  apply c₁.wf.induction v, intros x ih,
  simp only [circuit.eval_output, circuit.comp_val, circuit.comp_to_precircuit, precircuit.comp_deps, comp_dep, list.map_map, sum.elim_inl],
  congr' 1, rw list.map_eq_map_iff,
  rintros (y|y) hy,
  { simp, },
  { simpa using ih _ hy, },
end

@[simp] lemma circuit.comp_eval_inr_inr (c₁ : circuit α U V) (c₂ : circuit α W X) (f : W → U ⊕ V) (input : U → α)
  (x : X) : (c₁.comp c₂ f).eval input (sum.inr $ sum.inr x) = c₂.eval (λ w, c₁.eval input (f w)) (sum.inr x) :=
begin
  apply c₂.wf.induction x, clear x, intros x ih,
  simp only [circuit.eval_output, circuit.comp_val, circuit.comp_to_precircuit, precircuit.comp_deps, comp_dep, list.map_map, sum.elim_inr],
  congr' 1, rw list.map_eq_map_iff,
  rintros (y|y) hy,
  { cases H : f y; simp [H], },
  { simpa using ih _ hy, },
end

/-- Circuit with at most n-ary fan in gates -/
def circuit.bdd_fan_in (c : circuit α U V) (n : ℕ) : Prop :=
∀ v, (c.deps v).length ≤ n

lemma circuit.bdd_fan_in.comp {c₁ : circuit α U V} {c₂ : circuit α W X} {n} (f)
  (h₁ : c₁.bdd_fan_in n) (h₂ : c₂.bdd_fan_in n) :
  (c₁.comp c₂ f).bdd_fan_in n
| (sum.inl v) := by simpa [comp_dep] using h₁ v
| (sum.inr x) := by simpa [comp_dep] using h₂ x

structure circuit_computes {β γ : Type*} (f : (β → α) → (γ → α)) :=
(δ : Type)
(out : γ → δ)
(c : circuit α β δ)
(hc : ∀ (x : β → α) (y : γ), c.eval x (sum.inr (out y)) = f x y)

def circuit_computes.comp {β₁ β₂ β₃ : Type*} {f : (β₂ → α) → (β₃ → α)} {g : (β₁ → α) → (β₂ → α)}
  (hf : circuit_computes f) (hg : circuit_computes g) : circuit_computes (f ∘ g) :=
{ δ := hg.δ ⊕ hf.δ,
  out := λ y, sum.inr (hf.out y),
  c := hg.c.comp hf.c (λ y, sum.inr (hg.out y)),
  hc := λ x y, by simp [hf.hc, hg.hc] }

def circuit_computes.join {β₁ β₂ β₃ : Type*} {f : (β₁ → α) → (β₂ → α)} {g : (β₁ → α) → (β₃ → α)}
  (hf : circuit_computes f) (hg : circuit_computes g) : circuit_computes (λ x (y : β₂ ⊕ β₃), y.elim (f x) (g x)) :=
{ δ := hf.δ ⊕ hg.δ,
  out := λ y, y.elim (sum.inl ∘ hf.out) (sum.inr ∘ hg.out),
  c := hf.c.comp hg.c (λ x, sum.inl x),
  hc := λ x y, by cases y; simp [hf.hc, hg.hc] }

def bdd_circuit_computes {β γ : Type*} (f : (β → α) → (γ → α)) (n : ℕ) : Prop :=
  ∃ (c : circuit_computes f) [fintype c.δ], c.c.bdd_fan_in 2 ∧ by resetI; exact fintype.card c.δ ≤ n 

lemma bdd_circuit_computes.comp {β₁ β₂ β₃ : Type*} {f : (β₂ → α) → (β₃ → α)} {g : (β₁ → α) → (β₂ → α)} {n m} :
  bdd_circuit_computes f n → bdd_circuit_computes g m → bdd_circuit_computes (f ∘ g) (n + m)
| ⟨fc, I₁, fb, hfc⟩ ⟨gc, I₂, gb, hgc⟩ :=
by resetI; exact ⟨fc.comp gc, (infer_instance : fintype (gc.δ ⊕ fc.δ)), 
  gb.comp _ fb,
  by simpa [circuit_computes.comp, add_comm] using add_le_add hgc hfc⟩

lemma bdd_circuit_computes.join {β₁ β₂ β₃ : Type*} {f : (β₁ → α) → (β₂ → α)} {g : (β₁ → α) → (β₃ → α)} {n m} :
  bdd_circuit_computes f n → bdd_circuit_computes g m → bdd_circuit_computes (λ x (y : β₂ ⊕ β₃), y.elim (f x) (g x)) (n + m) 
| ⟨fc, I₁, fb, hfc⟩ ⟨gc, I₂, gb, hgc⟩ :=
by resetI; exact ⟨fc.join gc, (infer_instance : fintype (fc.δ ⊕ gc.δ)), 
  fb.comp _ gb,
  by simpa [circuit_computes.join] using add_le_add hfc hgc⟩

lemma false.well_founded {α : Type*} : well_founded (λ (_ : α) _, false) :=
well_founded.intro (λ a, acc.intro _ (λ _, false.elim))

def tt_circuit : circuit bool empty unit :=
{ deps := λ v, [],
  wf := by simp [false.well_founded],
  val := λ v hv, tt }

def and_circuit : circuit bool (fin 2) unit :=
{ deps := λ _, [sum.inl 0, sum.inl 1],
  wf := by simp [false.well_founded],
  val := λ _ (b : list bool), (b.inth 0) && (b.inth 1) }

structure circuit_family (δ : Type*) :=
(cct_size : ℕ → ℕ)
(ccts : ∀ (n : ℕ), circuit δ (fin n) (fin (cct_size n)))
(outs : ∀ (n : ℕ), list (fin n ⊕ fin (cct_size n)))


