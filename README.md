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
  - Instead of `iterate` and `comp` in the definition of `polytime`
    maybe have one constructor `iterate_comp` that takes care of the entire file (up to the usual iterate) for `polytime.basic`
    Because it seems we need to do that kind of stuff *anyway* in list_basis.lean


Note: › is frq