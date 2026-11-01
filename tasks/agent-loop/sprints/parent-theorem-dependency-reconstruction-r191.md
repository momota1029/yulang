# R191 — parent-theorem dependency reconstruction

Revision 1. Status: primary-owned replan after user direction; mathematical
objective and accepted source domain unchanged.

## Original roots

Use the exact declarations in `notes/theory/lean/YulangClosure/Contracts.lean`:

- `SourceProblem.InferenceSoundness` (`:128–130`): for every supported source,
  generated constraint problem and satisfying assignment, produce an original
  source derivation and `sameScoped` for that same assignment.
- `SourceScopedCoverage` (`:133–135`): independently construct a satisfying
  assignment for each original derivation and generated problem.
- `PrincipalCoverage` (`:138–144`): construct one principal solution and show
  every original source derivation factors through it by the original ordering.
- `InferenceTermination` (`:152–154`): prove accessibility of the actual
  inference transition relation from every supported initial state.

All four roots remain OPEN. Native correspondence is a later implementation
bridge, not a premise defining the abstract mathematical algorithm. The source
domain, Call/effect rules, quantifiers and shared witness remain unchanged.

## Required outcome

Produce a reviewed backward dependency map from those original roots to their
first independently defined semantic objects and owner obligations. For each
edge, identify its source authority, Lean declaration, exact unproved equation
or law, parent consumer, and what evidence would remove that edge. Separate
independent denotation/generation from source-rule induction, solution
coverage/principality, and the actual transition relation/termination.

Success is a concrete dependency graph whose next mathematical construction
can remove a named parent edge. Do not count helper lemmas, Lean theorem totals,
Rust identifiers, test totals or conditional premises as parent progress. If
the canonical mathematical objects are not independently defined, name that
definition boundary; do not start another constructor-specific conditional
proof that assumes it.

The sole report is
`tasks/agent-loop/history/parent-theorem-dependency-reconstruction-20261102-v2.md`.
No Rust audit, code change, build, test, environment, cache or scratch work is
authorized by this packet. Primary budget: 600 seconds; fresh independent
review: 600 seconds. No follow-up proof producer is admitted by this replan.
