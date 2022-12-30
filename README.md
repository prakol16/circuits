## TODOS:
  - Automate stack_rec conversion, deriving polytime
  - Automate deriving polycodable/stack_rec polytime given inductive type
  - Automate generation of composition lemmas
    - For polysize: use max instead of sum? (more aligned with Bellantoni and Cook paper)
  - Use nat's instead of trees? Avoids major refactor with encode but involves (somewhat) major refactor with mk_pair
        - Also significantly more annoying to show lists etc. are polynomial-sized
  - Add complexity_class_decodable class instead of making it a class for each complexity class
    - Use abbreviations e.g. polycodable = complexity_class_decodable PTIME
