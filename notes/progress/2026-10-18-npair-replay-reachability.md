# NPAIR local supplier and Replay reachability

Sprint `npair-operation-source-contract-and-replay-reachability-20261018`,
contract revision 3, SHA-256
`1fa25ac715f9bd583c7dc56e11b1fe027f71e953faac0fc6130b2e2b009ed94d`.
Baseline `759f9d0b784c71f19dc489199edf2d268174cbbc`. Parent
`CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` remains OPEN; original
conditions closed **0 -> 0**.

## Source-to-execution change

Before this change, the scoped source planner refused an Apply whose callee
resolved to a local name, so the existing private LocalUse/FreshUse path could
not reach the receive fixture's `g ()` call. The planner now follows only
Group/Ascription wrappers and empty Blocks by source indices, charging each
visited node to `SCOPED_WORK_LIMIT`. It records the exact terminal local-name
index on the private `ApplySourceInput`. A local with an annotation, an active
recursive initializer/Link, a CatchBinder, a Catch/If join, or a Block with
bindings remains refused.

`candidate_call::observe` rechecks that the saved index is an owned, scoped
Local Name in the exact LocalSource. During Apply admission,
`shadow_apply::admit_candidate_fact` requires the just-published
`LocalFreshRoute` to match that exact Name occurrence and local identity, with
no pending `LocalUse`. The preceding `Action::Local` creates its `LocalUse`,
captures the initializer graph, and calls `prepare_candidate_fresh_use` using
the Name occurrence's caller region. That operation freshens the owned scope
forest, remaps scoped input/scope transformers and demand roots, imports bound
evidence, restores captured bounds, links the actual fresh root to the Name,
and publishes the route before Apply admission. This is private candidate
source/constraint/propagation/execution evidence; it does not establish
semantic Call formation or any original theorem premise.

The LocalUse and LocalFreshRoute records remain fallible and capped at
`SCOPED_RECORD_LIMIT`; route capacity growth uses `try_reserve_exact`. Existing
GraphState accounting includes both retained vector capacities and each
retained graph/FreshUse map. The new Apply input field is charged through
`CandidateCall::State::bytes`; no extra retained wrapper list or traversal
stack was added. The existing structural Replay observer remains private,
opt-in, stderr-only, and semantics-neutral.

## Evidence and boundary

The source owner already authenticated LocalSource ownership, local slots,
constraint actions, capture regions, and FreshUse scope/input remaps. The prior
reviewed LocalUse/FreshUse identity and valid-state remap evidence was reused.
The withdrawn Vec prototype was not restored: this change adds no wrapper-path
Vec, and LocalUse/route allocations remain fallible, capped, and accounted.
Fresh compiler review is required on the exact frozen diff before executing
the fixture.

No Cargo/build/test/fixture command ran. No actual fixture execution or
demand-bearing Replay row is claimed. After CLEAN exact compiler review and a
fresh measurement of at least 120 seconds remaining in this lane, run at most
two focused commands (each <=120 seconds) against the pinned fixture with
`YU_CALL_REPLAY_OBSERVER=1`. If inference stops before observer emission, record
that obstruction and do not claim Replay coverage.

This is provisional candidate instrumentation/admission. Falsifier: the exact
received/choose fixture does not reach the authenticated local callee and a
demand-bearing Replay row, or a row fails the typed call/root/ordered-endpoint
checks. Cleanup owner: Luna; remove the provisional admission/observer changes
if the owner correspondence or semantics-neutrality check fails. No fixture,
expected output, diagnostic, public API, ordinary inference rule, or source
domain changed.
