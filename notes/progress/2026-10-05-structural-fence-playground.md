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
- Bounded false-rejection differential: the same 1,226 packages against six
  candidate one-node graphs (7,356 package/model checks); no `UNSAT` result
  rejected a candidate witness.
- `python3 -m py_compile tools/check_structural_fence_completion.py` and
  `git diff --check` pass.

This search does not prove completeness, explore all multi-node witnesses, or
establish that every `UNSAT` is correct. It is finite characterization evidence
for the reviewed theorem and a guard against the specific implementation
mutations above. It selects no production algorithm, resource rejection
policy, source mapping, effects semantics, or principal representation.

## Review and next gate

One independent `compiler_referee` review found the endpoint-reversal,
negative-coordinate, empty-Record, profile-limit, and rigid-namespace issues.
The primary repaired them and reran the focused and finite differential
checks. Narrow delta reviews confirmed closure of the negative-coordinate,
rigid-namespace, and malformed-rigid-instance findings with no new findings.
No broad compiler tests or performance measurements were run.

Next research gate: grow the independently enumerated graph oracle to small
multi-node regular assignments, preserve and shrink any new discrepancy, and
compare more generated SAT/UNSAT packages. Production integration remains
gated by the full Function/effect bridge, source adequacy, and principality.
