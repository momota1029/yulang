# R312 source/native handoff — revision 2

Sprint ID / contract revision and SHA-256: R312 / contract SHA-256 `e38ec894eecac29c07c8aa960f0785d2fd100c147f8c96b1affec09f88eea9bc`.
Assignment ID / handoff revision: R312-NATIVE / 2 (revision 1 was acknowledged before this sequential update).
Parent gate / original theorem and scope locator: unchanged R159 original source Union catalogue and child/result fields at its same extension. This is provisional runtime evidence only; it does not discharge a theorem or parent edge.
Baseline / direct dependency hashes: HEAD `d3136f276924a036af7e62eea6e13e63e2510155`; `program.rs` `9c280992897b5664fef12e38df8161c4f1561a2d69654b1f5e1146339a3ca903` (read-only, unchanged); `machine.rs` baseline `cf384ee9a8fe289f6906d464dbd8f5388e773e6a3e7037304760d007b5a4e46f`; Cargo.lock `de2c030452a0764cbeb459e2545585a880edc6683a8acceaea45276e24b67ca5`; `crates/yu-hir/src/module/local_source.rs` `7055975d582dfb198836c2aa659f8b8033c29dff419d522feea4fea4c42523d1`; `crates/yu-hir/src/module.rs` `6bf92c93fa37f425a7380248c12c50c0d04ea6eb282e76edb6df54e628260646`. Frozen Lean dependencies: `OriginalCalleeDelayProvenance.lean` `3acb041c530b19e78703b3f3030edd1b304ab7c20329974f0afc2d387428dbfe`; `OriginalNameForceExtraction.lean` `10ff6a2d4ac8a4a2c386396c495e0edfecc9bd4bb3ae40c8e0ab07e4cb0c7531`; R311 interpretation `7d230579d98b9034e62192330f98b2578629635e9810e7a7ff9195a29c813de6`; R311 resolution `33f55921d95dc87a7fde357df1d9514a4c01aa7159b654e0b1d21f6210206017`.
Role / actual worker ID / session / launch receipt: source/native implementer lane; `/root/r312_callee_native`; session/launch receipt unavailable to this child.
Requested model and effort / observed model and effort: Luna / high per fixed assignment; actual model and effort UNKNOWN in this runtime view.
Exact leased paths / authors: worker writes `tools/inference-playground/src/runtime/machine.rs`, this handoff, and `/tmp/yulang-r312-native/`; `tools/inference-playground/src/runtime/program.rs` was read-only. No descendants.
Outcome class: provisional source-native evidence.

## Achieved behavior and source/native correspondence

The test fixture is accepted by `CandidateInference::solve` without conflicts:

```yu
act io:
    our tick: int -> int
my make seed = { io::tick seed; \argument -> builtin_op::int_add seed argument }
my relay (thunk:[io] int) = make 1 thunk
my handle (thunk:[io] int) = catch thunk { io::tick(p), k -> handle { k 10 } }
my main = handle { relay { io::tick 2 } }
```

The actual owner chain observed is retained HIR Apply occurrence → compiled Apply argument label → saved `Frame::Callee` with caller environment → a Request while evaluating callee `make 1` → resume and consume that same Apply's saved frame → returned closure → exact argument Name lookup after Callee selection → real consume receipt → actual Force of the received Delay/view → Request inside that Delay → resumed saved ordinary `Frame::ValueEntry` returns through its retained Force receiver/formal. Final result is 11 and two Requests are observed. The test records the original entry receiver and the actual return execution owner separately: Request replay consumes the ordinary ValueEntry under another current invocation, so the evidence does not claim those IDs are equal. The completion observation is emitted only from actual ValueEntry dispatch when the retained `entry_receiver` equals the pending Force owner and the actual formal matches the call formal.

The test-only source-owner check resolves the exact Apply from `call_site.source_root` and occurrence in its retained `HirModule` local source, then verifies that this Apply owns the compiled argument label's exact HIR argument occurrence. It rejects a foreign separately-built HIR, a replaced Apply site, and an alternate Name label. Lookup collection covers every executed matching owner-qualified Name source occurrence; exactly one must exist, after Callee selection, under the same call invocation and original caller environment. The check resolves the exact formal cell there and compares its received value/view. A real post-dispatch consume receipt is captured from the receiving machinery and its raw receipt fields are checked for owner/view/source slot. For Execute, the exact receipt must precede one actual Force of a stored `ExecutableValue::Delay` with exact code/environment and view. The actual ValueEntry completion must carry the same pending lookup, receipt, Delay input value/view, saved receiver and formal; the output value is the resumed handler response 10.

Source constructors → constraints → propagation → consumer/native path: the fixture is accepted by the existing inference candidate path; this packet does not inspect or add solver constraints/propagation. Native execution consumes the real retained HIR/runtime program and normal source Apply/Name/Delay/Request/Resume machinery. All new observation state and capture code in `machine.rs` are private `#[cfg(test)]`; no production runtime behavior changed.

## Checks, limitations, and next step

Final focused check: `cargo test -p yu-playground --locked --offline --lib callee_argument_history_r312_` — exit 0, 2 passed, 0 failed, 91 filtered out. Final `git diff --check -- tools/inference-playground/src/runtime/machine.rs tasks/agent-loop/inbox/callee-argument-history-r312-source.md` — exit 0. Two intermediate Cargo attempts exposed a bad assumption about resumed owner identity and then a missing type alias; both were corrected. The final evidence preserves the actual owner transition. Full output summary is in `/tmp/yulang-r312-native/focused-check-r2.txt`.

This does not prove all-program behavior, solver success beyond the accepted fixture, complete NativeExtraction/History, original source typing theorem, independent A/B arm laws, world/license/future laws, R159 admission/checking, or production readiness. It does not tie the runtime observation to Lean `allocate_facts` or `OriginalNameForceExtraction`; proof lane must identify whether these exact Apply/Delay/Name fields satisfy any premise and list remaining premises (stable TODO `R312-NATIVE-TO-PROOF-1`). There is no evidence here for a general serialization or replay law. The Request/resume owner mapping is reported only as the actual saved `ValueEntry.entry_receiver` plus actual current return owner recorded at dispatch, with receipt/formal/site/value/view equality; no equality of those invocation IDs is assumed.

Coverage and falsifiers: exact same-HIR Apply/argument owner; foreign HIR; alternate Apply and alternate Name code label; early or duplicate Name execution (the complete occurrence collection must have cardinality one and order after Callee selection); wrong caller environment (the closure environment resolves no identical source cell); wrong wrapper Delay view (it differs from the actual received Force view); mismatched receipt, owner, code, environment, site, formal, value or view; and the callee Request missing, duplicated, or occurring after the same saved Apply frame's return. The fixture also requires the actual Force Delay to Request before its saved ValueEntry returns.

Known limitation: `SourceRootId` equality is required alongside occurrence/range checks. An earlier exploratory trace with equal occurrence ordinal/range and a different root was rejected as a source argument join; a later explicit mismatch assertion was unstable and is not claimed as a regression test or counterexample. The independent reviewer should still challenge the direct owner chain, especially whether the test's instrumentation capture and retained frame fields suffice for its stated bounded correspondence.

Before/after: before this packet, the available Name observer was a first matched Name lookup, without global duplicate/early rejection, post-dispatch receiving receipt, actual Force return, or callee Request while the saved Callee frame was pending. The fixture's prior Request sat in a body after Value entry. After R2, the test rejects these specific gaps for one accepted execution and records the actual receipt/Force/resume path. This is a narrower runtime evidence result, not a theorem closure.

Resource: fixed assignment ceiling 1800s; exact active seconds spent/remaining are UNKNOWN because runtime accounting is unavailable. No Astra resource used. Heavy Cargo slot is returned after this completed check.

Artifact hashes / frozen review target: `tools/inference-playground/src/runtime/machine.rs` SHA-256 `caa627ce1829122a22034d83eecdb258a161410444a390d786d4e7a3a8ac281c`; scratch receipt `/tmp/yulang-r312-native/focused-check-r2.txt` SHA-256 `86484f858459ef064d8265cbec178c864b68b8a7ed70f6928f8038fd5b3c9982`; handoff hash is reported with the submission. `program.rs` remains unchanged at its baseline hash. No Git operation performed.

Next related step inside existing envelope: freeze these bytes for a fresh independent source/native review; keep observations test-only. Reviewer should specifically verify that `pending Force owner == actual saved ValueEntry.entry_receiver` and formal matching are captured from the real frame dispatch, and assess whether actual callee Request/return ordering is correctly attributed to the same Apply. No further change to source syntax, expected output, diagnostics, domains, or runtime semantics is authorized by this packet.

Worker state / writes stopped / unresolved leases: after these handoff/scratch writes, no further writes; no descendants. Primary owns review/integration. Cleanup owner for provisional test instrumentation is Luna after evidence is consumed or a separately reviewed/authorized promotion.

Prior evidence reused/rejected: reused existing Callee call observation, actual machine `Frame::Callee`, receiving `consume`/raw receipt identity, ordinary Delay Force, and actual Request/resume continuation machinery. Rejected first-match-only and pre-dispatch-only R1 observations; rejected the old body-after-ValueEntry Request fixture; rejected use of same formal or occurrence ordinal/range alone as a source-owner join; did not use stubbed bind/install or fabricated receipts from the R305 Catch fixture.

New paths: `tasks/agent-loop/inbox/callee-argument-history-r312-source.md`; `/tmp/yulang-r312-native/focused-check-r2.txt`. Known disposable scratch: `/tmp/yulang-r312-native/`, primary-only hygiene.

Frozen handoff ID/revision/SHA-256: R312-NATIVE / 2 / compute on final bytes at submission.
