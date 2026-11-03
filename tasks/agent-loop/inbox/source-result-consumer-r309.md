# R309 native source-result consumer — frozen handoff r1

Sprint: `source-result-consumer-r309`, contract SHA-256
`1fd0a1685e69cfe7ac025dc779f60c51579d14876f09e4ac6613254c4c2df141`.
Baseline: `95207e05a`; original source Union → catalogue and child/result fields →
R159 are unchanged. Assignment: `/root/r309_native_flow`; handoff ID `R309-NATIVE`,
revision 1. Parent is the only Git integrator.

## Runtime and lease

Worker task identity: `/root/r309_native_flow`. Session-specific runtime session,
launch receipt, effective model and effort were not exposed to this worker and are
UNKNOWN. Requested lane: `gpt-6-luna` / high per the fixed sprint contract. No
model or effort claim is inferred from the request. Exact write leases used:
`crates/yu-solver/src/shadow_apply.rs`, this handoff, and
`/tmp/yulang-r309-native`. No other repository paths were written; no Git or child
processes were used. Writes to the two leased files are stopped after this frozen
revision. Only one Cargo process ran at a time; aggregate observed Cargo work was
under the 1800-second assignment bound (about 100 seconds including compile and
focused retries).

## Outcome and parent/source/native correspondence

Outcome class: `source-native-evidence` with a test-only implementation contribution.
The in-crate regression parses and lowers `my id x = x\nmy answer = id (id 1)`
once, obtains the `answer` definition's actual `LocalSource` body, and follows the
real outer Apply argument `LocalSourceIndex` to its `Group`, then follows
`Group.inner` to the nested Apply. Candidate solving receives that same HIR Arc.
The observation selects exactly slot-0 causes for those three actual occurrences
and borrows their original `SemanticFact` lower/upper `Term`s and direct source
origins. It rejects incomplete facts, origins, dependencies, Capture bounds,
FreshUse maps, or provider-route observations.

The check derives relation IDs from those exact cause-owned direct origins; it
never hard-codes row/relation ordinals. It follows retained native dependencies:

- The nested Apply's `FunctionPort(Result, Preserve)` child is consumed as the
  upper parent of its retained Replay, producing the nested result relation.
- The actual Group cause's Replay consumes that nested result as its positive
  lower parent and the Group's direct seed as its negative upper parent.
- The actual outer Apply's `FunctionPort(Argument, Swap)` child and the Group
  result are the distinct upper and lower parents of the outer Replay.
- The outer observation is tied to the actual source Call consumer: the consumer
  Apply occurrence and callee occurrence match the outer Apply and its retained
  source callee expression. Its native callee and demand remain full `Term`s.

The assertions preserve positive/negative Replay direction and relation-parent
identity. They do not equate a negative result Term with a positive argument
Term, do not reconstruct an absent edge, and do not consult or claim the stronger
unrelated `consumer_relation_join_complete` predicate. No natural inference,
source domain, expected output, diagnostic, or production semantic was changed.
This establishes the requested nested source → generated constraints → retained
propagation → typed FunctionPort/Replay consumer path for this concrete source
fixture. It does not establish public runtime execution semantics or any A/B
premise.

## Falsifiers and focused checks

The tests exercise wrong source slot, omitted Group cause, a nested call from a
different source call, a mutated Replay parent (`u32::MAX`), and a zero-row cap.
Each fails the same complete-chain checker. An established contradictory guard
fixture remains classified as a candidate conflict; it is not used as evidence
for the successful fixture.

Final check (exit 0):

```text
CARGO_TARGET_DIR=/tmp/yulang-r309-native cargo test --locked --offline \
  -p yu-solver --features shadow-apply-candidate --lib \
  r309_nested_result_consumer_test -- --nocapture

running 2 tests
...authentic_nested_result_crosses_group_and_reaches_outer_function_consumer ... ok
...nested_result_chain_rejects_wrong_slot_group_omission_and_cross_call_substitution ... ok

2 passed; 0 failed; 833 filtered out
```

The first command without `shadow-apply-candidate` failed because the candidate
modules are feature-gated. The first feature-enabled compile identified test-only
cause-accessor and HIR-Arc borrowing errors; those were repaired. An intermediate
wrong fixture selector and a non-conflicting `1 2` candidate were also corrected.
The final focused log is `/tmp/yulang-r309-native/focused.log`, SHA-256
`528dab3e8e41a29e517f69efcd54b519b838e93de2416fae3b02720f5e98cbf0`.
Build products under `/tmp/yulang-r309-native/` are disposable scratch. No
expectations or diagnostics were edited.

## Evidence reused, rejected, remaining premises

Reused read-only evidence: the R308 native investigator's authentic same-HIR
probe `/tmp/r309-result-flow/probe.rs` (SHA-256
`d1987a25561979e7a0717cd0b7f4da1968bfb8e8ce74aa5ecf549ae99482d0d1`) and result
`/tmp/r309-result-flow/result.txt` (SHA-256
`4a9e416a86e9b2657740b4df60e37a06cda72882c974c1c45d9ab1b087ff8e3f`). Its
reported chain was independently checked through the test's own authentic HIR
construction and exact relations. Ordinal values from that probe are not treated
as identities. R308's conditional proof handoff
`tasks/agent-loop/inbox/computed-call-union-clauses-r308.md` (SHA-256
`6c933233420820293d3b2fc1a18a01b017aec10920af31eae7e760f1a3fce6d8`) remains
conditional and supplies no q_c registration, source/native admission or proof
closure. No Simple-sub bypass was restored.

Direct source/dependency hashes at freeze:

- `crates/yu-solver/src/shadow_apply.rs` (candidate artifact): SHA-256
  `7362eb3ce2a943c0bde2ab3cdac05320838b849e7899a2fbfac71b519e04fde6`.
- `crates/yu-solver/src/candidate_source.rs`: SHA-256
  `bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49`.
- `crates/yu-hir/src/module/local_source.rs`: SHA-256
  `7055975d582dfb198836c2aa659f8b8033c29dff419d522feea4fea4c42523d1`.
- `crates/yu-solver/Cargo.toml`: SHA-256
  `aaf341e14643b73668552a3bf499f6410bdd0e9ad6ebeea1a5d6ef454d9494ed`.
- `Cargo.lock`: SHA-256
  `de2c030452a0764cbeb459e2545585a880edc6683a8acceaea45276e24b67ca5`.

Exact remaining owner TODOs requested by Luna:

- `R309-EI-OWNER` — source/descriptor owner: provide the original typed EI operand
  construction and source-owned q_c registration, instantiated from actual typed
  operands under the original scope. Required evidence is the source constructor,
  occurrence/terms, scoped record and original clause registration. Falsify with
  a reconstructed operand, mismatched occurrence/scope, or a clause absent from
  the authoritative source interpretation.
- `R309-NATIVE-LEAN-SERIALIZATION` — source/native bridge owner: define and check
  a general Lean export/serialization of the actual native fact causes, full
  Terms, typed FunctionPort direction, Replay parents and completeness needed to
  apply this bridge to R159. Falsify with lost polarity/parent/source identity,
  truncation accepted as complete, or an invented edge.

Neither TODO is discharged here. Original EI/GR1 construction and R159 admission
remain OPEN; this native fixture does not establish either. No new source domain,
semantics, authority, or lease is proposed.

## Artifact and hygiene

Only repository output paths are `crates/yu-solver/src/shadow_apply.rs` and this
exact handoff. New scratch path is `/tmp/yulang-r309-native/` (focused log plus
Cargo target products); it is disposable after primary review. The borrowed
`/tmp/r309-result-flow/` files predate this assignment and were not modified.
Fresh independent review is pending. Worker production claims stop at the
concrete structural source/native evidence above; the handoff is not self-review
or theorem closure.

## Revision 2 — bounded parent/endpoint repair attempt (2026-11-03)

This sequential revision follows the independent R1 review and Luna's repair
request. R1 remains preserved above with its original artifact hash and findings.

The R1 checker was not a complete causal-chain certificate: it ignored
FunctionPort parent identities, the inner Replay lower edge, and exact Replay
endpoint Terms. In response, a test-only revision temporarily snapshotted each
observed dependency's actual typed child/parent relation pairs and compared
FunctionPort projections and Replay inputs. The authentic nested fixture did
not pass the stronger chain check, so no complete checker or instrumentation is
retained. `crates/yu-solver/src/shadow_apply.rs` is restored byte-for-byte to
baseline `95207e05a` (SHA-256
`99d67895c250e5d79fb774728867fe2fc88c4dc22df9bfc38ac9fd1aeb0908e5`).

The concrete unresolved join is between the source Call and the FunctionPort
parent. In the same-HIR fixture `my id x = x; my answer = id (id 1)`, the inner
Call's native callee is Term 283, a positive live value variable at ordinal 8;
its native demand is negative-function Term 288. The observed FunctionPort
(Result, Preserve) parent relation is relation 31 with positive-function Term
279 as its lower endpoint and the same negative-function Term 288 as its upper
endpoint. Thus parent 31 is not directly the Call's callee Term. An observed
Replay has child relation 31, lower parent relation 24 and upper parent
relation 30; this suggests the route from the Call's live callee row to the
positive function parent, but this lane did not authenticate the exact endpoint
composition and source ownership for that bridge. Treating 279 and 283 as equal
would invent an edge. The outer FunctionPort has the analogous requirement.

The focused R2 command was
`CARGO_TARGET_DIR=/tmp/yulang-r309-native cargo test --locked --offline -p yu-solver --features shadow-apply-candidate --lib r309_nested_result_consumer_test -- --nocapture`.
The strengthened authentic-chain assertion failed while the existing wrong-slot,
Group-omission and cross-call negative cases passed. Logs are preserved in
`/tmp/yulang-r309-native/revision2-build.log` (pre-bridge attempt) and
`/tmp/yulang-r309-native/revision2-bridge.log` (bounded bridge repair attempt).
No test-only instrumentation or failed checker remains in the source artifact.
The R1 focused result is only evidence for its weaker gate; it does not cure the
reviewer's endpoint/parent counterexamples. No final green R2 test is claimed.

The original R1 TODOs remain open: `R309-EI-OWNER` for source-owned typed EI
operand/q_c construction, and `R309-NATIVE-LEAN-SERIALIZATION` for a general
checked export of native causes, full Terms, parent edges, typed endpoints and
completeness. The immediate native boundary is an authenticated exact bridge
from each real Call callee to the actual FunctionPort parent, including the
Replay endpoint composition and source-owned incidence. The original EI/GR1
construction, R159 admission, theorem closure, and cutover remain OPEN.

R2 artifact snapshot: restored baseline `crates/yu-solver/src/shadow_apply.rs`
SHA-256 `99d67895c250e5d79fb774728867fe2fc88c4dc22df9bfc38ac9fd1aeb0908e5`.
R2 handoff bytes are frozen by this revision's hash in the completion receipt.
Disposable scratch under `/tmp/yulang-r309-native/` includes Cargo targets,
`focused.log`, `debug1.log` through `debug4.log`, `revision2-build.log`,
`revision2-bridge.log`, and `shadow_apply.baseline.rs`; the last file is the exact
baseline copy used for restoration. Fresh independent review is still required.
