import data.list.basic
import data.polynomial.eval
import tree

namespace list

section all_some

@[simp] lemma all_some_nil {α : Type*} : (@list.nil $ option α).all_some = some [] := rfl

@[simp] lemma all_some_cons_none {α} (x : list (option α)) :
  (none :: x).all_some = none := rfl

@[simp] lemma all_some_cons_some {α} (x : list (option α)) (y) :
  (some y :: x).all_some = x.all_some.map (list.cons y) := rfl

@[simp] theorem all_some_of_map_some {α} (x : list α) :
  (x.map some).all_some = some x :=
by induction x; simp [*]

end all_some

end list

namespace tree

lemma left_num_nodes_le {α} : ∀ (x : tree α), x.left.num_nodes ≤ x.num_nodes
| nil := rfl.le
| (node _ a b) := nat.le_succ_of_le le_self_add

lemma right_num_nodes_le {α} : ∀ (x : tree α), x.right.num_nodes ≤ x.num_nodes
| nil := rfl.le
| (node _ a b) := nat.le_succ_of_le le_add_self

end tree

namespace polynomial

@[mono]
lemma eval_mono (p : polynomial ℕ) : monotone (λ n : ℕ, p.eval n) :=
begin
  induction p using polynomial.induction_on' with p q h₀ h₁ n a,
  { simp, apply monotone.add; assumption, },
  simp, apply monotone.const_mul _ (zero_le a),
  { intros x y hxy, apply pow_le_pow_of_le_left (zero_le x) hxy, }, 
end

end polynomial