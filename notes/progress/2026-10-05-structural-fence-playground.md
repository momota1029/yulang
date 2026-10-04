# Structural finite-fence executable playground

Date: 2026-10-05
Branch: `research/simple-sub-intrusion`
Classification: executable research characterization of the reviewed pure
structural FMP theorem; no production authority

## Goal and scope

The user authorized executable research models as part of proof search before
all successor soundness and principality gates close. This experiment turns the
profile construction in the reviewed
[finite-fence theorem](../../notes/design/2026-10-04-structural-fmp-fence-completion.md),
§§4–10, into a standalone checker. It accepts normalized finite pure
structural packages with flat shared descriptors, mandatory Records, fixed
heads with `+`, `-`, or invariant coordinates, exact equations, and per-root
rigid permissions. It is not connected to the production compiler and has no
effects, optional fields, extrema, source-adequacy, or principal-projection
semantics.

The checker builds the finite seven-distance closure, memoizes reachable
profiles before expanding recursive ports, and validates generated graphs
using the closure-independent coinductive validator from
`tools/check_preclosed_structural_witness.py`. A rigid-permission rejection
uses the reviewed same-address shadow result. Profile-budget exhaustion is a
separate `LIMIT` status and never means `UNSAT`.

## Executable findings

The first small counterexamples exposed implementation mistakes in the
candidate, not counterexamples to the theorem:

- endpoint reversal was accidentally implemented as variance conjugation,
  exchanging the symmetric `H`/`L` fence bounds;
- negative-coordinate closure reversed child endpoints and applied
  conjugation, reversing twice;
- the empty Record was accidentally classified as an atomic anchor before the
  Record case;
- profile-budget exhaustion while allocating start profiles escaped the
  `LIMIT` result path;
- a string-prefix encoding could confuse a fixed constructor head with a
  rigid leaf.

These were minimized to three small SAT packages: two distinct one-field
Records below one variable (whose common upper may be `{}`), one contravariant
Function comparison, and a recursive nonempty Record below `{}`. The checker
now has each as a focused regression. Rigid leaves use a distinct input class;
the reserved display prefix is rejected on ordinary terms.

## Checks

On 2026-10-05:

- `python3 tools/check_structural_fence_completion.py`: 13 focused packages;
  10 `SAT`, 3 `UNSAT`; every generated `SAT` graph passes the independent
  original-bound/equation validator; per-root permission and `LIMIT` cases
  pass.
- Exhaustive package generation over one variable, six endpoint terms, and
  zero through two inequalities: 1,226 packages; no generated witness was
  rejected by the independent validator.
- Bounded false-rejection differential: the 1,226 packages against every
  labeled graph with one or two nodes over atoms `A/B`, Record masks `{}` and
  `{a}`, Function `(-,+)`, and invariant `Box`. All 248 one-variable graph/root
  assignments were checked against each `UNSAT` package (265,856 checks); no
  false rejection was found.
- A two-root extension generated all 169 one-inequality packages over `X,Y`
  and the eleven corresponding flat endpoints. Every assignment of both roots
  into the same 127 labeled one/two-node graphs was checked for each `UNSAT`
  result (45,080 checks); no false rejection was found. This exercises shared
  graph nodes and cross-variable bounds without rigid leaves.
- The exhaustive two-root corpus was extended to all unordered pairs of
  distinct bounds: 14,196 packages (`2,562 SAT`, `11,634 UNSAT`). Every
  `UNSAT` result was challenged against all 490 root assignments in the same
  127 one/two-node graphs (5,700,660 checks); no false rejection was found.
- Four two-root constraint shapes were tested under all four combinations of
  `k` allowed/forbidden independently at roots `X` and `Y`. Including a rigid
  atom gives 151 one/two-node graph shapes; 5,830 graph/root assignments were
  screened, with per-root permissions applied before independent inequality
  validation.
- The focused structural rejection cases were checked against all exactly-
  three-node graphs in a package-matched signature: atoms `Int/Bool`, every
  Record mask over `{a,b}` with each field pointing at any graph node, Function
  `(-,+)`, and invariant `Box`. This gives 27,000 labeled graph shapes and
  810,000 graph/root checks across the atomic and overlapping-Record `UNSAT`
  cases; no bounded false rejection was found.
- Per-root rigid cases were also checked against all 6,859 three-node graphs
  over the small `A/B/k` signature and Record field `a` (617,310 graph/root
  assignment screens). A prior toy-signature pass was identified in review as
  vacuous for the `Int/Bool` and `{a,b}` rejection cases; the package-matched
  rerun replaces that weaker result.
- `python3 -m py_compile tools/check_structural_fence_completion.py` and
  `git diff --check` pass.

This search does not prove completeness, explore all multi-node witnesses, or
establish that every `UNSAT` is correct. It is finite characterization evidence
for the reviewed theorem and a guard against the specific implementation
mutations above. It selects no production algorithm, resource rejection
policy, source mapping, effects semantics, or principal representation.

## Review and next gate

Independent `compiler_referee` reviews found the endpoint-reversal,
negative-coordinate, empty-Record, profile-limit, and rigid-namespace issues.
The primary repaired them and reran focused, generated-package, shared-graph,
and per-root permission checks. Review also caught that the first three-node
structural signature missed the actual `Int/Bool` atoms and second Record field;
the 27,000-shape package-matched campaign above replaced it. Narrow reviews
closed the solver fixes, generalized enumeration/counting, permission
filtering, and this relevant-signature repair. No broad compiler tests or
performance measurements were run.

This oracle is complete only for the stated graph bounds, small signature, and
package families; it does not prove that a reported `UNSAT` is correct outside
these finite families. Rigid permissions are checked for a small targeted
two-root corpus, not the full 14,196-package family. The next inference
replacement gate should return to the remaining production-facing callback
and principality bridges; further structural model expansion is useful only if
it tests a specific open claim. Production integration remains gated by the
full Function/effect bridge, source adequacy, and principality.
