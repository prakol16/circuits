# Towards a proof of Cook-Levin in Lean

## Description of project

This project defines polynomial time computation and shows certain properties about such computation. It is heavily based off of the previous repository [here](https://github.com/prakol16/lean_complexity_theory_polytime_trees) and the analogous PR for primitive recursive functions [here](https://github.com/leanprover-community/mathlib/pull/16416). Unlike the previous repository, there is no explicit time model; instead we follow the footsteps of the mathlib's existing `primrec` definition and build an inductive definition of polynomial time functions.

An interesting aspect of this approach is that unlike previous approaches to formalizing Cook-Levin, we avoid Turing Machines entirely. Turing Machines are cumbersome and require several intermediate models of computation to be useful (e.g. mathlib has `TM0`, `TM1`, and `TM2`), which we would have to show are themselves polynomial-time preserving. With this approach, we can show CIRCUIT-SAT is NP-complete with just 3 models of computation, including circuits as a model of computation. We also introduce automation (the tactic `complexity`) to automatically close goals related to showing functions run in polynomial time.

## Structure

We first define an encoding of some basic types in `encode.lean`. This is the same thing as mathlib's `encodable`, but with the target as trees (thus, `tencodable`). Note that using trees gives very nice definitional equalities. For example, `encode (x :: xs)` is defeq to `encode (x, xs)`.

The files in `src/complexity_class` define a notion of function class that is closed under composition and contains some basic functions. It is essentially the class of functions which can be computed in "constant" time. In the future, this can serve as an abstraction that many other classes of computable functions (e.g. primitive recursive functions, recursive functions) can extend, so that "obvious" functions do not have to be reproven to be in the class.

The folder `src/polytime` builds results about polynomial time functions themselves.

Finally `src/circuits` -- still a work in progress -- builds results about circuits.

## Models of computation

### Tree-based

The main model of computation is based on binary trees, as in [the previous version of this repository](https://github.com/prakol16/lean_complexity_theory_polytime_trees). In particular, we define polynomial time functions as in Cobham's characterization with minor modifications:

```lean
inductive polytime : (tree unit → tree unit) → Prop
| nil : polytime (λ _, nil)
| id' : polytime id
| left : polytime (λ x, x.left)
| right : polytime (λ x, x.right)
| pair {f₁ f₂} : polytime f₁ → polytime f₂ → polytime (λ x, (f₁ x) △ (f₂ x))
| comp {f₁ f₂} : polytime f₁ → polytime f₂ → polytime (f₁ ∘ f₂)
| ite {f g₁ g₂} : polytime f → polytime g₁ → polytime g₂ → polytime (λ x, if f x = nil then g₁ x else g₂ x)
| bounded_rec {f} : polytime f → polysize_fun (λ x : tree unit, f^[x.left.num_nodes] x.right) → polytime (λ x : tree unit, f^[x.left.num_nodes] x.right)
```

The key property here is `bounded_rec` which states that if `f` is polynomial time, then so is `f^[n](x)` as long as this output has size bounded by a polynomial. Note that we use iteration rather than `tree.rec` since iteration is easier to reason about and to make the reduction to list-based polynomial time functions easier.


In order to state results about `n`-ary functions, we use the `function.has_uncurry` class. Thus, we might state a lemma like the following:

```lean
@[complexity] lemma list_append : ((++) : list α → list α → list α) ∈ₑ PTIME
```

This lemma is definitionally equal to `(λ (x : list α × list α), x.1 ++ x.2) ∈ₑ PTIME`.

### List-based

The list-based definition of polynomial-time functions is a predicate `polytime' : (vector (list bool) n → list bool) → Prop`, and has a very similar structure to mathlib's [existing definition](https://github.com/leanprover-community/mathlib/blob/master/src/computability/primrec.lean#L1188) of `primrec'`. Instead of `succ`, we have `cons`, and we also have `head` and `tail`. Finally, the recursion principle is `fold`, which states that folding over a list is polynomial time as long as the result has polynomially-bounded size.

We use the results from `catalan.lean`, which contains many results of independent interest related to the equivalence between binary trees and balanced parentheses, to encode trees and show that this model of computation is equivalent to the model based on binary trees. The final lemma we get is:

```lean
lemma iff_polytime {n : ℕ} {f : vector (list bool) n → list bool} : 
  polytime' f ↔ f ∈ₑ PTIME := ⟨to_polytime, of_polytime⟩
```

### Circuit-based

Finally, the current goal is to finish circuit-based computation. This is the lowest level of computation that we work with. However, unlike TM's, composing circuit computations is very straightforward: just "connect" the inputs of the next circuit to the outputs of the first circuit. We have a definition of circuits and circuit evaluations and a proof that circuits compose appropriately.

The eventual goal will be to reduce the list-based `polytime'` (and hence, equivalently the tree-based `PTIME`) to circuit computations. Once we can do that, it is relatively straightforward to show that CIRCUIT-SAT is NP-complete. While CIRCUIT-SAT being NP-complete is already a desirable result, if we want the most standard Cook-Levin (SAT or 3SAT is NP-complete), we can then use the standard polynomial time reductions to reduce CIRCUIT-SAT to 3SAT.

## Automation

There are a lot of routine tasks that can be automated using the tactic `complexity` (defined in `src/complexity_class/tactic.lean`).

### Basic idea

The basic idea of the tactic is to repeatedly apply any applicable rules tagged `@[complexity]` (using `apply_rules`). If this fails, we unfold `has_uncurry`, so that we get the definitionally equal statement of the function with only one argument, and attempt to apply a composition rule. We repeat this process until the goal closes or no progress can be made.

### Safe arguments

Sometimes, there are additional conditions that need to be satisfied beyond the structure of the function in order to run in polynomial time. For example, consider the `@[complexity]`-tagged lemma stating that we can iterate a polynomial time function polynomially many times:

```lean
@[complexity] theorem iterate_safe [polysize α] [polysize β]
  {n : α → ℕ} {f : α → β → β} {g : α → β} (hn : n ∈ₑ PTIME)
  (hf : f ∈ₑ PTIME) (hg : g ∈ₑ PTIME) (hp : polysize_safe f) : 
  (λ x, (f x)^[n x] (g x)) ∈ₑ PTIME :=
```

Notice we get an extra condition on `f`: `polysize_safe f`, which states

```lean
def polysize_safe (f : α → β → γ) : Prop :=
∃ (p : polynomial ℕ), ∀ x y, size (f x y) ≤ size y + p.eval (size x)
```

For `f : α → β → β`, if we think of `β` as a "state size", then `polysize_safe` states that `f` only grows the state by a polynomial in the first argument (i.e. independent of the current state size). We say `f` is *safe* in its second argument. This is precisely the notion of "safe" parameters presented by Bellantoni and Cook in their [characterization of PTIME](https://www.cs.toronto.edu/~sacook/homepage/ptime.pdf).

Discharging `polysize_safe` goals is especially amenable to automation because the result can often be inferred from the structure of the function itself. More precisely, Bellantoni and Cook show that composing functions such that the safe argument is inserted only into a safe location results in another `polysize_safe` function. 

### Recursor which allows time analysis

The ultimate goal is to build a `@[derive polytime]` handler that automatically shows "simple" functions (e.g. that use only structural recursion) run in polynomial time. To this end, we have a recursor called `stack_rec` (so called because we are more explicit about what goes on the stack and what does not). Such a recursor should be able to be generated automatically for any inductively defined `W-type`, but we have not yet written such automation.

Informally, we can think of recursively defined functions as: given input `x`, does some computation on `x` (`pre`), passes the result to the recursive call(s), and does some computation on the output of the recursive call(s) (`post`). For example, here are the definitions of `stack_rec` for `tree unit` and `list`:

```lean
def stack_rec {α : Type} {β : Type} (base : α → β)
  (pre₁ pre₂ : tree unit → tree unit → α → α)
  (post : β → β → tree unit → tree unit → α → β) : tree unit → α → β
| nil d := base d
| (x △ y) d := post (stack_rec x (pre₁ x y d)) (stack_rec y (pre₂ x y d)) x y d

@[simp] def stack_rec {α β : Type} {γ : Type}
  (base : α → β) (pre : γ → list γ → α → α)
  (post : β → γ → list γ → α → β) : list γ → α → β
| [] a := base a
| (x :: xs) a := post (stack_rec xs (pre x xs a)) x xs a
```

This is a very general notion of recursion, which includes most kinds of basic structural recursion. For example, almost all common list operations (fold, filter, map, zip, etc.) can be converted to use `stack_rec` in a very straightforward way. Similarly, binary number addition and multiplication are also in this form. A future goal is to do this conversion automatically (we will see in the next section that it is very mechanical).

Thus, showing that `stack_rec` runs in polynomial time (subject to certain `polysize_safe` conditions) allows us to do most structural recursion easily. Note that in some sense, `stack_rec` on trees is already the most "general" kind of recursion (branching factor > 1). In particular, since all data types are encoded as trees, if the encoding is natural, then any data type's `stack_rec` will be a function of `tree.stack_rec`. Thus, in the primrec mathlib PR, once we show that `stack_rec` is primitive recursive for trees, we can quickly port it to lists, nat, etc. In the polynomial-time case, unfortunately, it is a little more subtle, though it should still be doable. In this repository, however, we have simply manually proven `stack_rec` is polytime for lists (separately from trees).

#### Worked example (list.zip) 

Recall the definition of `zip` of two lists:

```lean
def zip {α β : Type*} : list α → list β → list (α × β)
| (x :: xs) (y :: ys) := (x, y) :: zip xs ys
| _ _ := []
```

How do we represent this using `stack_rec`? For a given list `(x :: xs)`, if the second argument is `l₂`, the argument we will pass to the recursive call is `l₂.tail` (more precisely, if `l₂` is of the form `(y :: ys)`, then we pass `ys`, and otherwise, we don't actually use the recursive result, so it doesn't matter what we pass).

Given the result of `ih := zip xs l₂.tail`, the value of `zip (x :: xs) l₂` is `(x, y) :: ih` if `l₂` is nonempty and `[]` otherwise.

Thus, we can prove:
```lean
theorem zip_eq_stack_rec (l₁ : list α) (l₂ : list β) :
  zip l₁ l₂ = l₁.stack_rec (λ l₂' : list β, []) -- base
    (λ x xs l₂', l₂'.tail) -- pre
    (λ ih x xs l₂', @list.cases_on _ (λ _, list (α × β)) l₂' [] (λ y ys, (x, y) :: ih)) -- post
    l₂ :=
by induction l₁ generalizing l₂; cases l₂; simp [*]
```

Note that `stack_rec` has the appropriate definitional equalities, so this result is always very easy to prove (usually just `induction`, followed by any necessary cases on the second argument, followed by `simp`).

Since `complexity` knows about `stack_rec`, it can automatically show the RHS of this theorem is in PTIME. In particular, this works:

```lean
example : (@zip α β) ∈ₑ PTIME :=
begin
  simp_rw (show @zip α β = _, from funext₂ zip_eq_stack_rec),
  complexity,
end
```

Note that the situation of rewriting to a certain form and running `complexity` is so common, we support the special syntax `complexity using` for it:

```lean
example : (@zip α β) ∈ₑ PTIME :=
begin
  complexity using 
    λ l₁ l₂, l₁.stack_rec (λ l₂' : list β, []) (λ x xs l₂', l₂'.tail)
    (λ ih x xs l₂', @list.cases_on _ (λ _, list (α × β)) l₂' [] (λ y ys (x, y) :: ih)) l₂,
  -- Must discharge the goal `zip l₁ l₂ = list.stack_rec ... l₁ l₂`
  induction l₁ generalizing l₂; cases l₂; simp [*],
end
```

## Files

Here is a more detailed overview of the organization of the project:
- `misc.lean`: Miscellaneous helpful lemmas about lists, vectors, etc.
- `tree.lean`: Defines some functions on binary trees. The same as [this PR](https://github.com/leanprover-community/mathlib/pulls/prakol16)
- `encode.lean`: Defines `tencodable`, which is `encodable` but  for `tree unit`'s
- `stack_rec.lean`: Defines `stack_rec` for many common types. In addition, shows the very important result that `stack_rec` on trees can be simulated in by an iterative process which keeps explicit track of the stack.
- `catalan.lean`: Combinatorial results about lists of balanced parentheses and their equivalence with trees.
- `complexity_class/`
    - `basic.lean`: Defines a functional class to be a collection of functions `f : tree unit → tree unit` closed under composition and containing some basic functions: `left`, `right`, `pair`, `nil`, `id`, `ite`, etc. Proves various composition lemmas needed before the tactic is set up.
    - `tactic.lean`: Defines the `complexity` tactic
    - `lemmas.lean`: A collection of basic facts about functions which can be computed in essentially constant time.
    - `stack_rec.lean`: Shows that a single step of the iterative method for computing `stack_rec` for trees runs in constant time. This is separated because there is a lot of casework (discharged automatically by `complexity`) that takes a while to elaborate.
- `polytime/`
    - `size.lean`: Defines what it means for a function to be `polysize_safe` (see above) and `polysize_fun` (have polynomial-size growth)
    - `basic.lean`: Basic facts about `PTIME`, the class of polynomial time functions, such as the fact that they are all `polysize_fun`
    - `stack_rec_size.lean`: Shows that intermediate results in `stack_rec` have polynomially-bounded size (will probably be refactored)
    - `lemmas.lean`: Lots of functions about lists and trees shown to be in PTIME
    - `list_basis.lean`: Proves the equivalence of `polytime'` (the list-based polynomial time definition) and `PTIME`
    - `example.lean`: Contains the `zip` example from this README
- `circuits/`
    - `basic.lean`: Defines circuits, circuit evaluation and composition of circuits
    - `circuit_encoding.lean`: WIP
