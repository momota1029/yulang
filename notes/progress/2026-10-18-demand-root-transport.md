# Demand-root transport implementation checkpoint

Sprint: `npair-demand-transport-correspondence-20261018`, contract revision 1,
SHA-256 `cff32b05adde3721c89eb86a97277cb56e9cfd7ee24c956bfd39a11f6e9d3422`.
Baseline: `f2d66da08`; author source tree was clean at `696f7d8d6` and the four
prior implementation pins matched the sprint contract.

## Candidate behavior

The candidate now exposes an opt-in, read-only `scoped_replay_demand_transports`
observation. It locates a retained `LocalFreshRoute` by the copied demand's
`use_instance`, reads the original demand from its original relation, and checks
the original-call/root pair against `negative_functions`. It then checks the
route's retained `terms`, `scoped_relations`, and scope/input remaps, and compares
the copied `NegativeFunction`'s four actual typed ports with all four mapped
source child terms. The existing stderr observer keeps the raw
`native_root_matches` value and adds route, relation, remap, and port evidence.
The example prints the same evidence to stdout.

No new storage was added. This preserves the existing source-to-constraint-to-
propagation route and the observed integer propagation. No solver, transport,
scope, root, consumer, or source behavior was changed. Authentication rejects a
wrong use identity, wrong root, or any substituted port. A focused regression
uses two separate module uses of the same source function and checks integer
propagation to both results.

## Prior evidence and boundary

Reused the pinned `FreshUse` construction: `scope_remap`, `terms`,
`scoped_relations`, `context_use`, and the atomic transfer into
`LocalFreshRoute.retained`. Reused the prior accepted fixture and its
source-owned formal Apply, retained Replay row, endpoint matches, and integer
propagation. Rejected raw root equality as the success criterion: the previous
`native_root_matches=false` remains reportable and unchanged.

This is provisional source evidence. It does not prove universal P3/P4
transport or close any original parent condition. The observer is falsified by
any candidate where a copied use/root or one of the four mapped ports disagrees.
Cleanup owner: Luna, after independent review and any successor acceptance.

## Verification and next step

No Cargo, test, or example command was run; frozen independent CLEAN review and
Luna's explicit runtime release are prerequisites. Only a static `git diff
--check` was run and it passed. Runtime remains unverified. The exact next step
is independent compiler review of these frozen bytes, followed by the two
contract commands once each if Luna releases runtime and fresh capacity is at
least 120 seconds.

The source-to-formal-introduction-to-received integer path remains as before.
Original parent conditions closed: 0. No extra storage accounting is needed.


## Review closeout

Independent proof/spec review was CLEAN for the conditional constructor theorem.
Independent compiler review did not accept the implementation: it found missing
Replay dependency ancestry authentication and a definitely failing pairwise-swap
unit assertion. The observer's map tuple is not sufficient to connect a source
relation to the selected Replay upper fiber. The candidate is frozen but
unapproved. No Cargo/test/example command ran; `git diff --check` alone passed.
Original conditions closed remain 0. Successor work must authenticate the actual
Replay dependency path and correct/execute the swap test before any runtime run.
