# Frozen implementation handoff

Sprint `npair-operation-source-contract-and-replay-reachability-20261018`,
contract revision 3, SHA-256
`1fa25ac715f9bd583c7dc56e11b1fe027f71e953faac0fc6130b2e2b009ed94d`.
Assignment `NPAIR-LOCAL-REPLAY-REACHABILITY-20261018`, handoff revision 1.
Parent `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`; parent remains OPEN,
original condition closure **0 -> 0**.

## Runtime and authority receipt

- Baseline: `759f9d0b784c71f19dc489199edf2d268174cbbc`.
- Requested role/model/effort: Luna implementation lane, Luna/high.
- Actual worker: `/root/npair_local_replay_path`, current session. Observed
  effective model/effort: UNKNOWN/UNKNOWN; no runtime metadata was exposed.
- Descendants/coauthors: 0. Git operations: 0. Fixture/expected-output/API/
  diagnostic/source-domain edits: 0.
- Lane authorization: <=900s; actual measured active-work receipt unavailable,
  so remaining capacity is UNKNOWN. The exact fixture command is not authorized
  until the frozen code receives CLEAN independent compiler review and the
  primary remeasures >=120s remaining.

## Outcome and parent application

Outcome class: provisional implementation / source-to-runtime path, not proof.
The scoped source collector previously refused the local callee in `g ()`.
It now indexes only Group/Ascription and empty-Block wrappers, charging every
visited node to `SCOPED_WORK_LIMIT`, and stores the terminal Local Name index in
the private Apply input. The Call observer validates that index against the
exact HIR-owned LocalSource. Apply admission then requires the last published
LocalFreshRoute to match the terminal Name occurrence and HirLocalId, with the
LocalUse continuation empty. Its route has already built authentic FreshUse
scope/input remaps, restored captured bounds, admitted the Name link and
published its fresh route. The Apply constraint is then admitted and enters the
existing propagation/execution path.

The collector refuses annotated local bindings, active recursive initializer
aliases/Link, CatchBinder, Catch/If joins, and Blocks with bindings. Existing
Replay observation remains private, typed, opt-in, stderr-only, and does not
affect solver state or results. This code establishes a candidate source and
native route, not semantic Call, Replay meaning, original-c membership,
N-Transport, F1/FK1, soundness, principality, termination, or parent closure.

## Frozen artifacts and checks

- `crates/yu-solver/src/candidate_source.rs`:
  `97d270953eb3b7c21cf47359ca7a865d6b22d00825ff37b29a03bef8de6ca35a`
- `crates/yu-solver/src/candidate_call.rs`:
  `da65afa35752b9247e899e420c1964b5290c9b2b72d7f208f68f916d5a0c38e3`
- `crates/yu-solver/src/candidate_scheme.rs`:
  `3c1b8f6a22faad0f5881a549c2ab86024ec692c6cad190b7e422bc4091463ffe`
- `crates/yu-solver/src/shadow_apply.rs`:
  `9fa2f3bc05ab1dbd93340b6c3edb107f72c2d7e08427dcc93117cf1b38c2efef`
- `crates/yu-solver/examples/research_source_registration.rs` (unchanged):
  `d76cbae29f5f095ffdb5068a49556149fe4a0fcc0f5d0702ff17ad71aed35f28`
- `tasks/agent-loop/fixtures/20261017-receive-choose.yu` (unchanged):
  `969e20e0f38a2c341a96ff4fe07028bf567ca134e0fb24602fadf6e4c723d9c0`
- Progress note `notes/progress/2026-10-18-npair-replay-reachability.md`:
  `51728cbb51552861641b6d06c065a73697c42e3011934dd6424b42d276445883`.

Direct dependency pins were checked against contract revision 3, including its
new Operation-construction input (`notes/design/2026-10-18-operation-contribution-formation-proposal.md`:
`4f0e7eeb5f02ae773725ca0086f441db5f5cc6734eaa3db17202d9bc49754fe3`). The
four mutable implementation files matched the contract's pre-edit pins at the
full baseline commit. Static diff review and `git diff --check` passed. No
Cargo/build/test/fixture command ran; therefore runtime exit/output/resources
and demand-bearing Replay-row presence are UNOBSERVED. No scratch files were
created.

## Reused/rejected evidence and provisional falsifier

Reused the reviewed LocalUse/FreshUse identity joins and valid-state scope/input
remap evidence in inbox `20261018-npair-swr1-output-origin.md`; that evidence
does not establish an executed route or theorem premise. Rejected the withdrawn
Vec wrapper prototype because its retained storage/scans were unbounded or
unaccounted. The new wrapper walk is index-based and cap-charged; Call input,
LocalUse and route capacities are accounted, and LocalUse/LocalFreshRoute
retention is fallible and capped at `SCOPED_RECORD_LIMIT`.

Provisional falsifier: the pinned fixture fails to reach the authenticated
local Name route or emits no demand-bearing typed Replay row, or the row fails
the existing exact call/native-root/ordered-endpoint checks. A command that
stops earlier only identifies that obstruction. Cleanup owner: Luna; revert
the provisional local-callee admission if independent review finds the source
owner or FreshUse correspondence incomplete, and keep the Replay observer
provisional unless its exact runtime evidence appears.

## Exact TODOs and next step

- `NPAIR-LOCAL-SUPPLIER-IDENTITY-20261018`: independent compiler reviewer
  checks wrong-owner/wrong-local, annotated target, recursive Link/CatchBinder,
  wrapper scopes, pending/failed LocalUse, FreshUse scope/input remap, and route
  publication before Apply admission. Owner: fresh compiler reviewer. Falsifier:
  any Apply admitted without its exact completed LocalFreshRoute.
- `NPAIR-REPLAY-RUNTIME-20261018`: after CLEAN review and a fresh >=120s lane
  measurement, Luna runs up to two focused <=120s commands on the exact fixture
  with `YU_CALL_REPLAY_OBSERVER=1`; record command, output/exit and resources,
  and whether a demand-bearing Replay row appears. Falsifier: early obstruction
  or no validated demand-bearing row; no coverage claim follows.
- `NPAIR-OP-SOURCE-WITNESS-20261017`: source-construction owner must still
  establish original fixed-c formation/elimination and the actual complete
  `A_decl`/Sigma/Lambda guarded licensed Written-s1 action against all original
  alternatives. This implementation does not discharge that semantic premise.

Worker writes stopped after this revision-1 handoff was frozen. Frozen code is
awaiting fresh independent compiler review; it is not self-certified or
integrated.
