# Sprint — provenance-complete Replay and concrete Operation rules

Contract revision: 2. Revision 1 SHA-256: 248f7949bb7b69875afd44c0965f878405b4563b14c68eb58a58aa28ae318455.

Revision 2 changes only the diagnostic test filter to include Rust's full candidate_scheme:: module path after independent review showed that --exact would otherwise select zero tests. Code leases, semantics, resources, and remaining commands are unchanged.

Status: ACTIVE, primary-authorized successor after rev8 closeout. Parent
`CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` remains OPEN. Original
quantifiers, source domain, accepted semantics and fixed `c` remain unchanged.
Candidate new semantics are allowed as a separate proposal under the user's
standing authorization, but are not adopted by this contract and cannot
retroactively prove the unchanged parent. Astra0.

## Outcomes and falsifiers

Implementation outcome: identify the actual positive-function ownership and
lower relation emitter in the failing Replay path. Test-only evidence must
retain, for each run, every positive Function node index, children and retained
term; all matches for the current lower root; lower relation pair/flow and
bound/emission provenance; and the source/FreshUse constructor and four ports.
Do not hardcode runtime term or relation numbers. Preserve the current
authentication predicate, all Module/Local siblings, and every existing
mutation control. A diagnosis is not a passing test. Repair only a demonstrated
fixture or retained-evidence defect. If the result requires changing ownership
semantics or authentication scope, stop for Luna's separate decision.

Proof outcome: produce the strongest concrete same-c Operation rule package,
not another free evidence wrapper. Specify a total source formation binding
before observations, actual complete R output at `out(d_A).Written[s1,j]`,
changed-interface W action, independent Z introduction/admission, dependent
domain/future maps, and actual consumer applicability, selection, residual,
pending/invalid and later-lower judgments. Define action-word normalization
and its evaluation/composition laws explicitly. Mark every premise original,
definitionally derived, or newly proposed; state whether the result is an
interpretation or changed semantics. The parent closes only if the original
`?e_Op` is genuinely derived for every original witness.

Falsifiers include zero or multiple exact term matches inconsistent with the
reported rejection; caller-owned function evidence absent from the callee
capture; a relation whose retained provenance disagrees with the selected
lower relation in that run; duplicate
Written occurrences collapsed; changed provider/world/interface with no full
map; unanchored Z without independent admission; or any original admitted
witness lacking same-c lift/reflection or real consumer parity.

## Exact leases and frozen inputs

Proof write leases:

- `notes/design/2026-10-18-operation-complete-source-semantics-candidate.md`
- `tasks/agent-loop/inbox/20261018-operation-complete-source-semantics-candidate.md`

Implementation write leases:

- `crates/yu-solver/src/candidate_scheme.rs`
- `crates/yu-solver/src/candidate_context.rs`
- `crates/yu-solver/src/shadow_apply.rs` (test-only source-constructor observation only)
- `tasks/agent-loop/inbox/20261018-replay-positive-provenance.md`

Luna alone owns these exact runtime paths, plus this contract and
`tasks/agent-loop/current.json`:

- `tasks/agent-loop/runtime/20261018-replay-positive-provenance.diagnostic.stdout.log`
- `tasks/agent-loop/runtime/20261018-replay-positive-provenance.diagnostic.stderr.log`
- `tasks/agent-loop/runtime/20261018-replay-positive-provenance.diagnostic.meta.json`
- `tasks/agent-loop/runtime/20261018-replay-positive-provenance.helpers.stdout.log`
- `tasks/agent-loop/runtime/20261018-replay-positive-provenance.helpers.stderr.log`
- `tasks/agent-loop/runtime/20261018-replay-positive-provenance.helpers.meta.json`
- `tasks/agent-loop/runtime/20261018-replay-positive-provenance.graph.stdout.log`
- `tasks/agent-loop/runtime/20261018-replay-positive-provenance.graph.stderr.log`
- `tasks/agent-loop/runtime/20261018-replay-positive-provenance.graph.meta.json`
- `tasks/agent-loop/runtime/20261018-replay-positive-provenance.example.stdout.log`
- `tasks/agent-loop/runtime/20261018-replay-positive-provenance.example.stderr.log`
- `tasks/agent-loop/runtime/20261018-replay-positive-provenance.example.meta.json`

Baseline source pins: scheme `ebbfa6da533a6c90df9b34075c397ebe5dbf9a9bac991e6f853138c5df1f71ab`;
context `67f831ac89800e065684cb3358e5b456d7e1b6e0b20f7cb9f3d4e1fc2f0e2b1a`;
shadow apply `396b288b53be76631cd0a5d748b7f19c6d3a73fc42e35001c503bed468ecc996`;
source `1a65c7afb02a4afd538a34c34086108959579e06aafe8fbcab8ad6a6b3a65f3e`;
call `e038ad0dfc4b12bd0d513d6cd6b34cee6b2b062d8b33368bc1c0dcdef980d479`.
Rev8 diagnostic receipts and proof comparison are frozen in its closeout and
history. Revalidate all pins before either lane writes.

Proof comparison dependencies to retain in the author note's manifest:
reviewed rev7 comparison `notes/design/2026-10-18-operation-fixed-c-rule-completion-options.md`
(SHA-256 `5aeeb0a116a4bb05bf7f247bb559c622eab5856ac1c0d9852700dbfc6c564a73`);
rev8 concrete-but-incomplete candidate
`notes/design/2026-10-18-operation-fixed-c-rule-completion-options-r2.md`
(SHA-256 `b8a23a5a075d1cac5c60e969086063cabd977c22acefe7eb73c7f21ad68901b3`);
rev8 closeout (SHA-256
`e557f8f9ddfd760f89ba057de17e6a2b0ff141c9297b02ac354f28b2cfd5b19f`);
the inherited IF construction (`278034197a90eab6e62a073545c09dd14415a0353f58aa3b3cc122a6af945d98`)
and Operation image (`4fe70b18cad9ded249869b21b84bbf26e2a5f95320f79632a29a5071ddb1c4e9`).
Record the exact remaining governing-source pins used from the inherited
32-entry manifest; do not infer source authority from those hash receipts.

## Stages, review and resource envelope

Implementation Luna/high author600s: add exact test-only provenance census;
freeze; fresh independent review; one diagnostic command (max120s). If it
identifies a fixture/retention defect, repair only that defect and freeze for
another independent review; then run helpers, graph tests and example once
each, sequentially. No retries. Total runtime480s; one heavy process at a time.

Proof Sol/high author600s: finish action-word formalization and construct the
complete rule candidate across all original alternatives and consumer cases;
apply results back to original `?e_Op`. Freeze one coherent note/handoff and
STOP for fresh independent semantic/proof review (180s).

Implementation reviews: 240s total across instrumentation and any repair.
Integration reserve: 120s. New total envelope **2220s**: implementation600 +
implementation reviews240 + runtime480 + proof600 + proof review180 +
integration120. Charge full author grants when launched. No prior rev8 seconds
roll over. Astra0, no descendants, maximum one heavy Cargo process. Reviewers
are fresh and never authors. Runtime sequence fails closed at first nonzero.

No test or runtime before the first frozen instrumentation review is CLEAN.
The diagnostic is a closed observational attempt: its original assertion stays
intact, and a nonzero exit still counts as diagnostic evidence if all required
census/provenance data is emitted. It is not retried unchanged. The four exact
commands, each with a 120-second timeout, are frozen here:

1. Diagnostic attempt, allowed only after the instrumentation review is CLEAN:
   `timeout 120s env YU_CALL_REPLAY_OBSERVER=1 cargo test --offline -p yu-solver --features shadow-apply-candidate candidate_scheme::authentic_demand_capture_tests::retained_demand_transport_authenticates_distinct_uses_and_rejects_wrong_use_or_root --lib -- --exact --nocapture`
2. Helper suite, only after a demonstrated fixture/retention repair is frozen
   and its independent review is CLEAN:
   `timeout 120s cargo test --offline -p yu-solver --features shadow-apply-candidate authentic_demand_capture_tests --lib`
3. End-to-end graph test, only after the same repair gate:
   `timeout 120s cargo test --offline -p yu-solver --features shadow-apply-candidate candidate_graph_call_authenticates_fresh_use_demand_transport_and_rejects_swaps --lib`
4. Accepted source example, only after the same repair gate:
   `timeout 120s cargo test --offline -p yu-solver --features shadow-apply-candidate accepted_scoped_formal_demand_replay_propagates_to_received_result --lib`

Each verification command runs at most once; a nonzero exit closes that
sequence immediately. No changed filter, retry, assertion weakening or
additional command is authorized by this contract.
No semantic adoption, checker relaxation, assertion weakening, row filtering,
or production promotion is authorized. A semantic change request returns to
Luna with the exact changed judgment and accepted-source consequences.

Next material consultation: actual zero/ambiguous/caller-owned diagnosis, a
source-qualified counterexample, a requested semantic/ownership change, lease
or resource expansion, or coherent closeout.
