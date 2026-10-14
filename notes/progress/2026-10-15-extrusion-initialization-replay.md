# Native extrusion initialization replay

Date: 2026-10-15
Branch: `research/simple-sub-intrusion`
Baseline: `c3c0fbdf542c63577f75140cf278d40af51f20c7`
Status: implemented and independently reviewed local native gate; parent
H1/H2/U and production/F5 remain OPEN, H3/P disabled

## Change and authority

`candidate_extrude` previously stored and transported copied incoming
Allowances without scheduling their comparisons with current source lowers.
It now retains each exact installed incoming `BoundKey`, finishes every
selected bound, origin/fiber transfer and parent/output group, then calls
the existing opposite-bound replay. Both production callers already run
inside the owning typed drain. No separate solver or graph scan is added.

Authority: contextual attachment/admission §§2,4,6; selected residual-lineage
current/future fan-out; top-level inference principles §§1–3. A bounded
read-only architect adjudication confirmed that exact reuse of this selected
transition needs no new durable semantic decision. The next-action selector's
initial provisional-only recommendation was resolved at those actual approved
carrier owners; this does not promote a source H2 theorem.

The [constructive invariant](../theory/2026-10-15-extrusion-initialization-replay-invariant.md)
shows why only incoming keys need retention: selected-bound copies are fresh
and one-sided; every initialized opposite pair includes an incoming upper.
The final phase therefore visits every actual lower/upper fiber combination
at these owners, preserving ordered contexts, both relation parents, exact
keys, source unions and separate view lineages. Its children are queued
before the rewritten Value is appended; descendants may run later. Existing
origin-association evidence gaps remain explicit.

Source constructors/constraints are unchanged. The bridge here is native
construction → exact bound transport → contextual Replay → typed queue/drain.
Authentic source eligibility, all-history completion, full Call, hygiene,
soundness and principality are separate obligations.

## Review and repair

Mode: M2; existing authority, intended private behavior, local native owner,
hot path. Convergence: no accepted blocking/major finding on the frozen local
proof/code, with focused runtime evidence and baseline failures accounted for.

The constructive `prover` lane ran alongside an independent read-only
falsifier and the implementation lane. A fresh `compiler_referee` reviewed
the frozen proof, native diff and new regression. A separate
`performance_auditor` reviewed the native diff and direct resource/replay
owners. Neither reported a proof/native-code blocker or major finding.
Requested proof routing was Sol/high; effective model/effort metadata were
unavailable, so no observed-setting claim is made.

The first owning-module run exposed one introduced test integration failure:
the opposite-tail fixture called extrusion directly, then opened a Fresh
transaction while its newly queued comparisons still lacked a drain owner.
The semantic reviewer classified this as major. Pre-write `spec_auditor`
review approved routing its first successful setup through ordinary
`constrain_live_value` into a level-0 receiver. This invokes the same positive
level-0 copy, completes queued work, and preserves every assertion and the
later injected-failure transaction. Semantic delta review closed the finding.
The earlier clean performance scope remained unchanged in that repair round.

## Cost and checks

For K retained incoming events, D physical opposite-bound visits and P new
fiber-pair candidates, additional metadata/fiber work is O(K+D+P), plus
existing source unions/interner/journal work. A distinct nonempty source union
of S entries sorts in O(S log S). Extra local scratch is O(K), and retained
replay bookkeeping/children are O(D+P) plus payloads. Repeated physical keys
still cost visits and empty operations; replay heads suppress repeated old
Cartesian expansion. With K=0 the added vector allocates nothing. Allocation
failures propagate and every local scratch charge is released on return.

Six serialized Cargo invocations, `CARGO_BUILD_JOBS=2`; test threads limited
to one. Exact checks, in execution order:

1. `cargo test -p yu-solver --features shadow-apply-candidate structural_value_extrusion_replays_initialized_allowance_fibers -- --test-threads=1`
   — new test passed; unselected integration binaries ran zero tests.
2. `cargo test -p yu-solver --features shadow-apply-candidate --lib candidate_effect::tests:: -- --test-threads=1`
   — before fixture repair: 24 passed, 4 failed, 2 ignored.
3. Same module command at isolated detached baseline `c3c0fbdf5`, with
   `CARGO_TARGET_DIR=/home/momota1029/rust/yulang/target`
   — 25 passed, 3 failed, 2 ignored; identical canonical failures below.
4. Same module command on final repaired candidate
   — 25 passed, 3 failed, 2 ignored; the introduced failure is closed.
5. `cargo test -p yu-solver --features shadow-apply-candidate --lib structural_value_extrusion -- --test-threads=1`
   — both existing observer and new regression passed.
6. `cargo check --workspace` — passed without warnings.

`git diff --check` passed. No broad test suite, benchmark, performance sample,
exhaustive probe or timing claim. The new regression covers reused/remapped
symbolic lowers, two copied view lineages, transported parents, nonidentity
ordered contexts/source retention, completed drains and later lowers. It does
not directly enumerate every fiber product or assert every queue position;
those general local claims use the reviewed constructor/consumer proof.

## Baseline residuals and next owner

Three unchanged failures occur identically at the baseline and final candidate:

- `raw_and_canonical_effect_roots_replay_late_conflict_after_parent_copy_intrusion`;
- `multiply_originated_bound_keeps_future_conflict_paths_through_extrusion_and_intrusion`;
- `views_keep_fresh_use_ownership_and_intrusion_rollback_restores_relations`.

Their relevant copies generate no incoming replay keys. The semantic owner
audit finds reciprocal type-bound setup without authentic qualifying
Value-reference SCC provenance under the selected intrusion rule. Their
assertions remain protected; a source-qualified fixture/implementation bridge
is required before deciding their repair. Owner: `candidate_effect.rs` test
construction and `candidate_intrusion.rs` occurrence qualification. No
whole-module green or full source theorem is claimed.

Records synchronized: `tasks/current.md`, `tasks/research-lab.md`,
`tasks/effects-handler-next.md`, `notes/design/INDEX.md` and the proof note's
review/implementation handoff. No semantic authority changed. Future work
must consume this implemented activation owner, retain the original source
H1/H2/U gates, and establish source qualification for the baseline regressions
without substituting a type-bound SCC criterion.
