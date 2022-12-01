import tree
import complexity_class.basic

@[user_attribute]
meta def complexity_class_attr : user_attribute :=
{ name := `complexity,
  descr := "lemmas usable to prove a function is primitive recursive" }

@[user_attribute]
meta def primrec_attr : user_attribute :=
{ name := `primrec,
  descr := "lemmas usable to prove a function is primitive recursive" }

@[user_attribute]
meta def polytime_attr  : user_attribute :=
{ name := `polytime,
  descr := "lemmas usable to prove a function is primitive recursive" }

namespace tactic

meta def is_tencodable (e : expr) : tactic bool :=
(do
   e' ← infer_type e,
   cache ← mk_instance_cache e',
   (cache', s) ← instance_cache.get cache ``tencodable,
   return tt) <|> (return ff)

-- meta def get_num_params (s : expr) : tactic ℕ :=
-- -- TODO: This should be based on the type of `s`, not the fact that `s` is a lambda function
-- do  guard s.is_lambda <|> fail "Not a lambda function",
--     mv ← mk_meta_var s.binding_domain,
--     e ←  instantiate_mvars (s.instantiate_lambdas [mv]),
--     f ← mfilter is_tencodable e.get_app_args,
--     return f.length

/-- Compute the maximum number of arguments subject to the conditions that
  only encodable and non-dependent arguments can be counted -/
meta def get_num_params_aux : expr → list expr → tactic ℕ
| tp (x :: xs) :=
do tp' ← whnf tp reducible,
  (do guard tp'.is_arrow,
    to_expr ``(tencodable %%tp'.binding_domain) >>= mk_instance,
    (+1) <$> get_num_params_aux tp'.binding_body xs
  ) <|> (guard tp'.is_pi >> get_num_params_aux (tp'.instantiate_pis [x]) xs)
| tp [] := pure 0

meta def get_num_params (s : expr) : tactic ℕ :=
do guard s.is_lambda <|> fail "Not a lambda function",
   mv ← mk_meta_var s.binding_domain,
   e ←  instantiate_mvars (s.instantiate_lambdas [mv]),
   let args := e.get_app_args,
   let fn := e.get_app_fn,
   -- Special casing `tree.node` because it is always called with argument `unit` TODO: a better way?
   if fn.const_name = ``tree.node then return 2
   else do
    tp ← infer_type fn,
    get_num_params_aux tp args

#check expr.is_constant

inductive tactic_classes
| prim | poly | computable

-- returns (function, complexity class, true if predicate false if function)
meta def get_goal_uncurry_base_fun : tactic (expr × expr × bool) :=
(do
  `(@complexity_class.mem _ _ _ _ _ (@function.has_uncurry_base _ _) %%f %%C) ← target,
  return (f, C, ff)) <|>
(do
  `(@complexity_class.mem_pred _ _ _ (@function.has_uncurry_base _ _) %%f %%C) ← target,
  return (f, C, tt))

meta def rw_lemmas : list name × list (expr ff) :=
([``complexity_class.mem, ``complexity_class.mem_pred], [``(complexity_class.mem1_iff_mem), ``(complexity_class.mem1_iff_mem_pred)])

meta def tactic_classes.attr_name : tactic_classes → name
| tactic_classes.prim := primrec_attr.name
| tactic_classes.poly := polytime_attr.name
| _ := default

meta def fail_lemmas : list name :=
[``complexity_class.const, ``complexity_class.mem.pair]

def comp_lemmas : bool → list name
| tt := [``complexity_class.const, ``complexity_class.mem_pred.comp, ``complexity_class.mem_pred.comp₂, ``complexity_class.mem_pred.comp₃]
| ff := [``complexity_class.const, ``complexity_class.mem.comp, ``complexity_class.mem.comp₂, ``complexity_class.mem.comp₃, ``complexity_class.mem.comp₄, ``complexity_class.mem.comp₅, ``complexity_class.mem.comp₆]

/-- Uncurries the target so that `polytime (λ (x : α) (y : β), ...)` becomes `polytime (λ (xy : α × β), ...)` -/
meta def uncurry_target (md : transparency) : tactic unit :=
do fail_if_success get_goal_uncurry_base_fun,
   dsimp_target simp_lemmas.mk (rw_lemmas.1 ++ [``function.has_uncurry.uncurry, ``id]) { md := md },
   first (rw_lemmas.2.map $ λ e, to_expr e >>= rewrite_target)


meta def try_comp (md : transparency) : tactic ℕ :=
do fail_lemmas.mfoldl (λ (_ : unit) x, fail_if_success (do
    x' ← resolve_name x,
    e ← to_expr x' tt ff,
    apply e { md := md })
   ) (),
   old_goal ← target,
   (target_fun, C, is_pred) ← get_goal_uncurry_base_fun,
   let comp_lemmas : list name := comp_lemmas is_pred,
   n ← get_num_params target_fun,
   guard (0 < n ∧ n < comp_lemmas.length),
   s' ← to_expr $ expr.const (comp_lemmas.inth n) [],
   apply s' {md := md},
   try `[ any_goals { apply_instance, } ], -- why is this necessary??
   (fail_if_success (uncurry_target md >> target >>= λ t, unify t old_goal md)) <|>
    focus1 (apply_rules [] [complexity_class_attr.name] 50 { md := md } >> done),
  return n

meta def auto_computable (md : transparency := reducible) : list (tactic string) :=
[
  apply_rules [] [complexity_class_attr.name] 50 { md := md }
                        >> pure ("apply_rules with " ++ (to_string complexity_class_attr.name)),
  uncurry_target md >> pure ("uncurry_target md"),
  try_comp md >>= λ n, pure ("apply comp" ++ (to_string n))
]

/- Given a goal of the form `a P b`, if `new_tgt` is a pexpr, say `a'`, changes
  the goal to `a' P b` and adds the goal `a = a'` -/
meta def rw_arg_ext (new_tgt : pexpr) : tactic unit :=
do tgt ← target,
   guard tgt.is_app,
   let arg₁ := tgt.app_fn,
   guard arg₁.is_app,
   let arg := arg₁.app_arg,
   n ← mk_fresh_name,
   to_expr ``(%%arg = %%new_tgt) >>= assert n,
   focus1 (symmetry >> tactic.funext),
   swap,
   resolve_name n >>= to_expr >>= rewrite_target

namespace interactive

setup_tactic_parser

meta def complexity
  (bang : parse $ optional (tk "!")) (trace : parse $ optional (tk "?")) (rw_tgt : parse $ (tk "using" *> texpr)?) (cfg : tidy.cfg := {}) :
  tactic unit :=
let md              := if bang.is_some then semireducible else reducible,
    core := tactic.tidy { tactics := auto_computable md, ..cfg },
    trace_fn        := if trace.is_some then show_term else id in
/- Make sure assumptions and goals are in the right form before we start -/
do try `[simp only [complexity_class.prop_iff_mem, complexity_class.mem1_iff_mem] at *],
  rw_tgt.elim skip (λ rw_tgt', rw_arg_ext rw_tgt'),
  trace_fn core

meta def clean_target : tactic unit :=
(expr.clean <$> target) >>= unsafe_change

end interactive


end tactic

attribute [complexity]
  complexity_class.const
  complexity_class.mem.pair
  complexity_class.mem.fst
  complexity_class.mem.snd
  complexity_class.mem_pred.ite

@[complexity]
lemma complexity_class.id' {α} [tencodable α] (C : complexity_class) :
  C.mem (λ x : α, x) := ⟨_, C.id, λ _, rfl⟩

example (C : complexity_class) : C.mem (λ (x : ℕ × ℕ), (x, x.2)) :=
by { complexity, }
