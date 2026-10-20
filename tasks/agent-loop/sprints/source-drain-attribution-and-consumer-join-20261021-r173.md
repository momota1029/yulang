# R173 source-drain attribution and consumer join — candidate contract

Status: **CANDIDATE** until a fresh prospective review is CLEAN and Luna records
activation. This candidate grants no worker, write lease, compiler execution or
probe by itself.

Branch: `research/simple-sub-intrusion`  
Baseline: `7ec64a378` (R172 reviewed checkpoint)  
Contract revision: 1  
Parent theorem: `notes/theory/2026-10-15-computation-forwarding-preservation.md` §§1,6–7,
SHA-256 `d732980d7706538fe18b5d8de312e9a2b6367ec6638ab938b239d46272624e79`.

## Original outcome and success evidence

Preserve the original forwarding theorem's source domain, quantifiers, shared
satisfying assignment, open incoming E, arbitrary finite chains/repeated calls/
simultaneous entries and every finite prefix. Do not narrow the accepted source
domain or alter inference semantics. R173 targets the unchanged R171
`terminal`/`relay` fixture and the missing R169/R172 source-fact → selected
seed → provider Capture/own maps → actual forwarding consumer association.

Decisive known owner: `start_typed_drain` calls
`candidate_context_seed_with_formal`, then uses `item.relation.or(seed)`. Replay
children enter with a relation and acknowledgement already present, but still
create an occurrence-matching Origin. R172's exact-hash reviewed query correctly
reports this attribution as UNKNOWN and did not run its conditional probe.

Success requires one of:

1. A borrowed typed certificate records the source cause/task, incoming relation
   and replay owner, created seed, and actually selected relation at the owning
   transition; a source-directed query follows that certificate through the
   same provider's Capture, own FreshUse maps, and exact A_F consumer relation,
   preserving alternatives and ordered Replay inputs; or
2. The proof lane establishes the first owner that cannot retain/discriminate
   this association and supplies a concrete falsifier.

Certificate absence or bounded-resource failure remains observationally
unavailable and must not change admission, propagation, inference, diagnostics
or publication. This is finite source/native progress only; no universal A/B
theorem or production gate closes.

## Two continuing lanes

Proof lane: one constructive proof producer continues R172 revision 2 from the
exact source/Replay callers. Prove certificate faithfulness for direct-source
and Replay invocations, multiple Origins/relations, and relevant failure/unwind
paths; apply the result to the same provider/consumer spine and original parent.
An exact obstruction is a useful result; occurrence equality or a successful
probe alone is not.

Implementation lane: Luna/high owns the smallest private inert certificate at
the actual seed-selection transition and a typed borrowed view through provider
Capture/maps/consumer. Derive every field from its owner. Do not use it to choose
or validate solver behavior. No public API or source-syntax change.

Prior evidence: R171 confirms source membership and one successful candidate
inference for the unchanged fixture; R172 proof rev2 has a CLEAN review and
establishes source facts plus static direct-seed existence while retracting
direct-drain attribution. R172's query/harness and handoff have exact-hash CLEAN
review; they expose unavailable attribution and the probe remains NOT_RUN.
R169/R70/R71/R165/R166/Replay and the original A/B/F1/FK1 gates remain OPEN.

## Frozen inputs and dependencies

- Unchanged fixture `tools/inference-playground/examples/r171-formal-name-forwarding.yu`,
  SHA-256 `cb2fff33a1ab983a932064cc1699d9f4f4a8d5e00d52986525884d42bc58234f`.
- R171 source proof `notes/theory/2026-10-21-r171-forwarding-instance.md`,
  SHA-256 `d19b5ceb2c1ace95ce2cc49bdd6c35ef4bd4de223f07e181a472a037a35a133b`.
- R172 proof rev2 note SHA-256
  `885ca6ca2eba9937cd7bc81ffb6bd384e8fa96d17cc26392b76e7de4a9876488`;
  handoff SHA-256 `ef35a47437ba1477736f895de4168a8fa8e9f0c43511dd620c9f486891dba1d8`.
- R172 CLEAN query code `crates/yu-solver/src/shadow_apply.rs`, SHA-256
  `13ae8de60293b91e24659090649ff84002f5632a8909451d3f7bd8492b61bea5`;
  implementation handoff is in `tasks/agent-loop/inbox/20261021-r172-implementation.md`.
- Baseline owners: `lib.rs` SHA-256
  `c75bf47b3d0d87e99d4365a587e6b90d5d05d05c335db16880cb2943b8b25985`,
  `candidate_context.rs` `d884c20a98140da2a737d65f61faa97491bd9a2af7870bf3f0ea7dd428e9ffeb`,
  `candidate_scheme.rs` `9569e7cc2ba7152cafe1273fba279a8511fe56aa39358798f3e4586c10ede225`,
  and `shadow_apply.rs` as above.
- Active design authority: user-approved top-level inference principles
  `notes/design/2026-10-11-yulang-inference-top-level-principles.md` and
  `rules/design-authority.md`; the proposed certificate is private observational
  evidence only, not an algorithm/semantic decision.

Any baseline, source, fixture or authority change requires a sequential contract
revision and fresh review. Preserve three UNKNOWN legacy reservations and all
unrelated R152–R163 work.

## Exact leases if activated

Luna may write only:

- `crates/yu-solver/src/lib.rs`
- `crates/yu-solver/src/candidate_context.rs`
- `crates/yu-solver/src/candidate_scheme.rs`
- `crates/yu-solver/src/shadow_apply.rs`
- `tools/inference-playground/examples/r173_source_drain_attribution.rs`
- `notes/theory/2026-10-21-r173-source-drain-attribution.md`
- `tasks/agent-loop/inbox/20261021-r173-implementation.md`
- one reviewed conditional probe's exact receipts under
  `tasks/agent-loop/probes/20261021-r173-provider.{stdout,stderr,status}`
- dedicated build artifacts `target/r173/` only if the probe gate is met.

Proof worker may write only:

- `notes/theory/2026-10-21-r173-source-drain-attribution-proof.md`
- `tasks/agent-loop/inbox/20261021-r173-proof.md`

No tests, broad builds, Yulang2/Y3 runtime, evaluator, external oracle, nested
CLI, network, background service, or unrelated source changes. The unchanged
R171 fixture stays read-only.

## Permissions, review and resources

Proposed hard cap **4200 active seconds**: preparation/authority reconciliation
240; proof 1200; Luna implementation 1500; independent reviews 720; one
conditional exact Y3 inference probe 300; closeout 240. Astra 0, no descendants
or carryover. A probe is allowed only if source occurrence, created/selected
seed, same provider Capture/maps and consumer relation are all represented in the
reviewed query with complete per-component evidence. Otherwise record NOT_RUN.

At most one narrowly scoped `cargo run --offline --locked` diagnostic may be
considered after independent review of exact code, harness, fixture and command
pins. This is inference evidence, not a test or proof of the universal parent.
No probe authorization follows from contract review alone.

Fresh independent review is required for the proof artifact and coherent code/
harness/query. Luna integrates only CLEAN reviewed exact paths, after checking
the full outbound range. Re-read runtime/lease evidence before activation; the
dispatcher does not grant leases or start workers. No writer may alter a frozen
review target.

Stop on ambiguous source or owner identity; certificate not tied to selected
seed; altered solver decision behavior; incomplete required joins; writer
conflict; changed dependency; exhausted budget; or user STOP. Preserve all
parent gates OPEN absent genuine proof closure.

## Integration outcome

Before/after evidence is the exact R172 status (`UNKNOWN`, no probe) versus a
reviewed source task → selected relation certificate → same provider/Capture/
maps → forwarding consumer association, or a specific owner obstruction.
Record requested and observed runtime models separately, current worker STOPPED
receipts, hashes and probe status in compact current state. The next dispatcher
consultation occurs at the first material counterexample/authority/lease change,
integration seam or sprint end.
