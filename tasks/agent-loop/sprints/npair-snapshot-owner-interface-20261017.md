# Sprint: qualify the NPAIR snapshot owner interface

ID: `npair-snapshot-owner-interface-20261017`
Status: ACTIVE; revision 2 is the current Luna-authorized bounded repair contract.
Parent: `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`, OPEN.
Primary and sole Git integrator: Luna.

## Fixed outcome

Qualify whether a one-shot structural validator can borrow one stable,
read-only, successful native snapshot and completely enumerate its structural
evidence without cloning the solver or inventing semantic facts. Produce an
owner-by-owner field-to-accessor table, proposed borrowed interface,
deterministic shared-witness traversal and complete work/storage accounting.
Then have an independent proof lane check mutation exclusion, complete evidence
coverage and certificate lifetime against the pinned owners. If a required
field, accessor or mutation/lifetime invariant is absent, name that exact
blocker and leave implementation waiting.

This does not resume the unresolved Operation source constructor. The original
`eta_op`/`realization_op` input remains WAITING for the actual adopted supplier;
no repeated source census, transport attempt or compiler implementation is in
scope.

## Baseline, authority and dependencies

Baseline: `7a281f6e4ecfc34dc9b9a722714d845e205e17bd`.

Previous one-shot structural Draft:
`notes/design/2026-10-17-npair-one-shot-structural-validator-contract.md`,
SHA-256 `2cf0d473f0c3a3f75474e54a99b5c1d4470ab338320272445eae0a5fe263e23f`.
Operation-supplier boundary proof:
`notes/theory/2026-10-17-npair-operation-contribution-supplier.md`, SHA-256
`1ee864b00d61b774e56c5a965a062448151652ad45ab4ec8956e1f02e7fd685b`.
Forward native evidence proof:
`notes/theory/2026-10-17-npair-forward-source-witness-realization.md`, SHA-256
`1d2c827cdf7661cc77a9edbb869bffd3cdcca7b51afba418789eaae9abf3cb3a`.

Exact read-only source owners to inspect and pin:

- `crates/yu-solver/src/lib.rs` / `InferenceSession`:
  `2c1fff385e5270ef7b7eb5fc4d9ed5f6edb6a4c01886887b183401212c5f398f`.
- `crates/yu-solver/src/candidate_effect.rs` / effect `State` and Permission,
  domain and view storage:
  `11a1477ff2c35c03dccb70bdc6121d89d3ced9fadb1921cb8cf8cd5c093b07fb`.
- `crates/yu-solver/src/candidate_context.rs` / context `State`, admissions,
  emissions, relations, Origins and Replay premises:
  `72da8a6e7b3f04ed3f7054b6151410c7d2b35f9f91b756ade1f6f008244c1ce6`.
- `crates/yu-solver/src/candidate_scheme.rs` / `GraphState`, route lifetime
  and canonicalization:
  `52b7281946de755003ee8f3b3d18cbc2df6cc6db5566b4e5ecf391b74a92640a`.

If another owner defines a directly consumed field or mutation boundary, pin
that exact file before relying on it and return to Luna if doing so expands the
four-owner scope. Distinguish existing immutable accessors from proposed
getters; a proposed borrow interface is not an implemented guard.

## Readiness lane — Luna/high first

Maximum 240 active seconds. Write only:

- `notes/design/2026-10-17-npair-snapshot-owner-interface.md`
- `tasks/agent-loop/inbox/20261017-npair-snapshot-owner-interface.md`

Inspect the four exact owners and return:

1. A table of every required field and its owning struct, current visibility,
   current read accessor/borrow, mutation points, rollback/truncation owner and
   whether the existing borrow covers the full relevant snapshot.
2. The smallest proposed owner-local borrowed aggregate/interface spanning the
   complete relevant evidence and source-state identities, or an exact missing
   field/access blocker. Do not make the aggregate public unnecessarily.
3. A definition of qualifying evidence and complete enumeration, including raw
   occurrence versus canonical representative, every relevant Origin,
   admission/emission, actual FunctionPort premises and both ordered Replay
   inputs. Preserve distinct occurrences and alternatives.
4. A deterministic iterative shared-witness traversal. Account premise and edge
   inspections, repeated visits, alternative expansion, work-stack capacity,
   witness storage and allocated capacity with checked arithmetic. Numeric
   execution limits remain a later separately reviewed gate; no unbounded
   scan, unique-node-only accounting or whole-solver clone.
5. Snapshot/certificate lifetime: the borrow must identify the owning state and
   route; its temporary result cannot outlive that borrow or survive rollback,
   slot reuse or canonicalization changes. If simultaneous sessions can be
   confused, show how owner identity prevents cross-state mixing.

This is design/readiness only: no code, tests, builds, probes or execution.

## Independent proof lane — after Luna STOP

Role `prover` (Sol/high), maximum 240 active seconds, at most four stages.
Write only:

- `notes/theory/2026-10-17-npair-snapshot-borrow-enumeration.md`
- `tasks/agent-loop/inbox/20261017-npair-snapshot-borrow-enumeration.md`

Independently check that the proposed borrow excludes every relevant mutation,
exposes all required evidence without omissions or cross-session mixing, and
expires before rollback/reuse. Verify the traversal accounts repeated scans,
branches and allocation capacity and checks both Replay premises. Clearly
separate access that exists today from proposed accessors. A documented
proposal is not a runtime guard, implementation theorem or code authorization.
If any condition fails, return the exact proof obligation/owner and no
validator implementation claim.

## Review, stop and resource envelope

After both authors STOP, fresh sequential reviews, each up to 60 seconds:

- compiler_referee: exact source-owner correspondence and borrow/lifetime
  proof;
- architect: owner responsibility, state identity and resource accounting;
- spec_auditor: exact one-shot structural-only gate and exclusions.

Fresh cap is exactly 720 seconds: Luna readiness 240, independent proof 240,
reviews 180, coordination 60. Astra 0. No reserve and no automatic extension.
Stop at an exact owner-interface blocker or cap; do not transfer unused time.
Preserve three historical UNKNOWN reservations, board quarantine and unrelated
dirty `authentic-source-and-forward-handler-20261017.json`.

No compiler lease, tests/builds/probes/Cargo/source execution, source admission,
`At`, N-Ingress, later-lower subscription, subtraction, N-Transport, receive
consumer or production change. A complete owner interface would establish
readiness only; any executable contract, code or resource limits require a new
reviewed gate. `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` remains OPEN.

## Revision 2 — Luna bounded review repair

Revision 1 remains preserved in Git history and governed all author/review work
through compiler-referee STOP. On the compiler-referee findings and the
selector's bounded recommendation, Luna revises this contract only to repair
the leased readiness Draft and handoff. No new source owner, implementation,
execution, or theorem claim is authorized.

- Readiness remains Luna's exact two-file lease, with a total 300s ceiling:
  the original 240s plus one 60s repair allocation.
- The proof consumed 176s measured and was charged 180s within its 240s cap;
  its recorded 60s unused capacity is the source of the repair allocation.
  Sprint total remains 720s: coordination 60, readiness 300, proof 180,
  compiler review 60, architect review 60, spec review 60. No reserve.
- Repair only these compiler-referee findings: mark unavailable
  OwnerEmission/ExtrusionLink/FreshUse antecedents as rejected/Pending unless
  independently authenticated; include live `InferenceSession.bounds` and
  `effect_bounds` plus checked physical-slot resolution; withdraw universal
  mutation-exclusion/readiness claims and leave same-owner enforcement and
  transitive `candidate_intrusion` mutation analysis as unresolved prerequisites.
- Keep the proof artifact byte-frozen. No `candidate_intrusion` source read is
  authorized by this revision.
- After readiness STOP, the remaining architect and spec-auditor 60s reviews
  inspect the amended readiness bytes and explicitly disposition all three
  compiler-referee findings. The executable interface and parent remain OPEN.
