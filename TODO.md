## TODOS:
  - Automate stack_rec conversion, deriving polytime
  - Automate deriving polycodable/stack_rec polytime given inductive type
  - Automate generation of composition lemmas
    - For polysize: use max instead of sum? (more aligned with Bellantoni and Cook paper)
  - Use nat's instead of trees? Avoids major refactor with encode but involves (somewhat) major refactor with mk_pair
        - Also significantly more annoying to show lists etc. are polynomial-sized
  - Add complexity_class_decodable class instead of making it a class for each complexity class
    - Use abbreviations e.g. polycodable = complexity_class_decodable PTIME
  - All the stack_rec's, polysize_safe etc.-based lemmas should have a stronger version (not available to automation) that uses `polysize_fun`
    - Relies on the property that the function has some self-similarity properties i.e. if the size is big at some intermediate stage,
    the *result* will be big from some starting stage
  - Finset stuff (all functions out of fintype's are in PTIME) should be defined using finitely supported (i.e. equals some const. outside support) functions; generalizes better
  - Speeding up automation
    - Each tagged lemma should store what the function application symbol is (if it is constant); when we run the tactic, that rule should be tried first
      - Order of priority: rule whose head application matches the current head application; `comp` if the first goal is closed by `assumption` or a rule; everything else
    - Ideally runtime should be linear in expression size
  - Fix looping bug with unknown predicate -> to_bool -> not unified (maybe: in the fail_if_success step, try to apply the to_bool lemma as well before unification)