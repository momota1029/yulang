# R40 typed Result consumer — frozen handoff

Sprint: `application-result-formation-20261018-r40`, contract revision 1,
`tasks/agent-loop/sprints/application-result-formation-20261018-r40.md`,
SHA-256 `a1ca3da89e79c7722f2f4e4a228086db360f0279ea1ee7e31ae6b970315eaa45`.

Assignment `R40-TYPED-RESULT-CONSUMER`, handoff revision **2**. Parent: full
Yulang inference/evaluator theorem and unchanged Simple-sub A/B scope,
quantifiers and source domain; all gates remain OPEN, parent conditions 0 -> 0.
Baseline `887eed4370278cd9e789fb2b9b10ff58369da540`.

Author/writer: `/root` (Luna primary), session
`current-conversation-2026-10-18`; requested Luna/high, observed effective
model/effort UNKNOWN/UNKNOWN. Exact output leases:

- `notes/progress/2026-10-18-typed-result-consumer-r40.md`
- `tasks/agent-loop/inbox/20261018-typed-result-consumer-r40.md`

This revision supersedes handoff revision 1 while preserving its bytes at
`tasks/agent-loop/inbox/20261018-typed-result-consumer-r40-rev1-snapshot.md`,
SHA-256 `4f32771591b51fadf514f21c90819951e3142cb76a8262ca2cd7e070dfff3c38`.
The paired note snapshot is
`notes/progress/2026-10-18-typed-result-consumer-r40-rev1-snapshot.md`,
SHA-256 `eb816bb306a9a8b068bfb786f7b45d3e24a968f3c96f81972477d6692d748170`.

Outcome class: **source-native evidence**, read-only and candidate-only. Current
artifact SHA-256 `71b7cae74f965f08e8c2877072ca179e47de5d4e05b335c19d95c7deb53ca2ea`.
It traces exact q from source Apply emission through q's negative Function
demand, typed drain, covariant `FunctionField::Result`,
`FunctionPortOperation::Preserve`, retained `Dependency::FunctionPort`,
Context/Dispatch, helper Function result endpoint and the retained-copy branch
where extrusion rewrites the pair. It distinguishes q's negative Value
endpoint in `NativeInterface.result` from the negative Function demand in
`NativeInterface.demand`. It does not establish ordinary source `Desc` formation
or semantic complete-Call result/future interpretation.

Independent compiler review revision 1 returned **MINOR corrections required**
with no blocking or major native-edge finding. It verified the substantive q
chain and identified two textual faults: the `NativeInterface` field swap and
the malformed `candidate_call.rs` digest. Revision 2 fixes both. Luna compared
the field names to `shadow_apply.rs:1862-1864`, corrected the digest to the
actual SHA-256, and rechecked all five Rust contract pins plus both revision-1
snapshots. These are minor-only factual corrections under
`rules/orchestration-budget.pre-sprint.md` §Finding batching and convergence
control; no code or semantics changed. The reviewer’s evidence was fresh and
did not rely on R39. The R39 edge-supplying reviewer was not assigned.

The first remaining semantic owner edge is the original Application/`Q_q`
derivation connecting this structurally propagated body Result to the complete
Call `Comp(E_q,A_q),o_q`, with its authentic ordinary `Desc` owner, sort, scope
and ordered dependent telescope. The proof lane is deriving that formation
judgment independently. No source program, compiler test, build, Cargo, CLI or
runtime was executed. Inputs and exact line locators are in the frozen artifact
and R40 contract. Rust paths are pre-existing dirty, unknown-author inputs and
were not changed. The NO_SAFE_CODE_SLICE finding remains for those paths.

Native 900-second grant charged; active duration unmetered. No descendants or
scratch outputs. The two leased files are frozen at revision-2 hashes; writer
STOPPED. Luna retains current-state, review, integration and Git ownership.
