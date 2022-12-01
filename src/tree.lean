import order.basic
import data.tree

namespace tree
variables {α : Type*}

/-- The number of internal nodes (i.e. not including leaves) of a binary tree -/
@[simp] def num_nodes : tree α → ℕ
| nil := 0
| (node _ a b) := a.num_nodes + b.num_nodes + 1

/-- The number of leaves of a binary tree -/
@[simp] def num_leaves : tree α → ℕ
| nil := 1
| (node _ a b) := a.num_leaves + b.num_leaves

/-- The height - length of the longest path from the root - of a binary tree -/
@[simp] def height : tree α → ℕ
| nil := 0
| (node _ a b) := max a.height b.height + 1

lemma num_leaves_eq_num_nodes_succ (x : tree α) : x.num_leaves = x.num_nodes + 1 :=
by { induction x; simp [*, nat.add_comm, nat.add_assoc, nat.add_left_comm], }

lemma num_leaves_pos (x : tree α) : 0 < x.num_leaves :=
by { rw num_leaves_eq_num_nodes_succ, exact x.num_nodes.zero_lt_succ, }

lemma height_le_num_nodes : ∀ (x : tree α), x.height ≤ x.num_nodes
| nil := le_rfl
| (node _ a b) := nat.succ_le_succ
    (max_le
      (trans a.height_le_num_nodes $ a.num_nodes.le_add_right _)
      (trans b.height_le_num_nodes $ b.num_nodes.le_add_left _))

/-- The left child of the tree, or `nil` if the tree is `nil` -/
@[simp] def left : tree α → tree α
| nil := nil
| (node _ l r) := l

/-- The right child of the tree, or `nil` if the tree is `nil` -/
@[simp] def right : tree α → tree α
| nil := nil
| (node _ l r) := r

/- Notation for making a node with `unit` data -/
localized "infixr ` △ `:65 := tree.node ()" in tree

/-- Recursion on `tree unit`; allows for a better `induction` which does not have to worry
  about the element of type `α = unit` -/
@[elab_as_eliminator]
def unit_rec_on {motive : tree unit → Sort*} (t : tree unit) (base : motive nil)
  (ind : ∀ x y, motive x → motive y → motive (x △ y)) : motive t :=
t.rec_on base (λ u, u.rec_on (by exact ind))

lemma left_node_right_eq_self : ∀ {x : tree unit} (hx : x ≠ nil), x.left △ x.right = x
| nil h := by trivial
| (a △ b) _ := rfl

end tree