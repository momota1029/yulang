Sprint R256 / current Tuple source-to-runtime audit

Outcome: solo primary read-only obstruction map; current source pins were read
at baseline `93daff511`. No code lease, tests, builds, sample executions,
subagents, independent review, or parent-gate closure.

Source correspondence:

- Parenthesized comma syntax becomes ordered `LocalSourceForm::Tuple`; narrow
  ordinary-HIR projection declines it, while `solve_mode` selects LocalSource
  and permits the owned placeholder errors.
- Candidate `Work::Visit` does not traverse Tuple children, and `Work::Finish`
  returns unavailable for Tuple. `candidate_value_graph::retain_source` also
  omits Tuple child incidence.
- Native ordered terms and indexed live comparison exist in R253/R254.
  `candidate_scheme::Node`, graph export and `yu-types` have no Tuple
  constructor; runtime compilation refuses Tuple and runtime values have no
  product case.

Parent application: Types remains blocked at candidate collection. Next code
design must cover ordered child visits/effect edges and source Value reachability,
then scheme/FreshUse, closed types, and ordered resumable runtime construction.
R168 prospective review remains OPEN; this result supplies no compiler
permission. Console imports/host output and all broader proof gates remain
separate and OPEN.

Checks: current-source reads and Git blob IDs only. No tests, builds or
executions. Output note:
`notes/theory/2026-10-21-r256-tuple-source-runtime-obstruction.md`.
