# Replay ancestry authentication candidate

Sprint `npair-replay-ancestry-authentication-20261018`, rev1. Parent
`CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` remains OPEN; original
conditions closed 0. This is an unreviewed source-evidence candidate.

## Implementation

The private observer now carries the exact Replay child/lower/upper relation
IDs and both input `BoundKey`s. Authentication requires the exact retained
source relation in one FreshUse route, its copied map, a unique
`Dependency::Transport` FreshUse edge with matching `use_origin` and witness
keys, and the exact `Dependency::Replay` row. The ancestry walk admits only
typed `Derived`/witnessed `Transport` edges, checks relation pairs and root
updates, and fails closed on cycles, multiple incoming/next edges, missing
witnesses or unsupported edge kinds. The selected upper must still name the
copied demand root. All four ordered `FunctionPort` children must have the
selected upper as parent, the expected operation and typed Value/Effect kind,
and distinct relation IDs. The route map still checks all four reconstructed
term ports, scope and input maps. Failed authentication exposes no FreshUse or
port relation IDs. Raw `native_root_matches` remains a separate false value.

The focused source fixture checks two distinct use/route identities and integer
lower propagation to both results. Added falsifiers substitute use, root,
source call/snapshot, Replay child/lower/upper, BoundKeys and sibling Replay
metadata. The swap helper now asserts all-port rejection plus exactly two
changed positions and two untouched matches; its test name is covered by the
prescribed `authentic_demand_capture_tests` command.

No source admission, inference, constraint, solver, root transport, scope or
consumer behavior was changed. No storage was added; ancestry traversal uses
relation-count bounded allocation-free scratch. Observer results use transient
strings only to expose exact `BoundKey` debug representations.

## Evidence boundary and next step

No Cargo, test, build or example command ran during authoring. `git diff
--check` passed. Fresh independent proof/compiler review and the three
single-run primary commands remain required. This does not establish the
original fixed-c association, `At(D,c,delta)`, source/native theorem, or any
original condition.

Next in-envelope step: freeze these exact bytes for fresh proof/compiler
review; only after both are CLEAN and Luna records capacity may the primary run
the three commands in the sprint contract once each.


## Compiler-review closeout

The proof/spec review was CLEAN for the conditional diagnostic theorem. The
independent compiler review blocked runtime: it found conflated source/copied/
Replay identities, the wrong FunctionPort parent, missing endpoint/transformer
and captured snapshot/fiber authentication, incomplete scoped-flow equations,
and negative tests that did not mutate the claimed evidence. The swap helper
is corrected and selected by the helper-filter command; both integer results
and raw mismatch remain asserted. No runtime command ran. This candidate is
unapproved, parent closure remains 0, and the exact blockers are recorded in the
primary closeout.
