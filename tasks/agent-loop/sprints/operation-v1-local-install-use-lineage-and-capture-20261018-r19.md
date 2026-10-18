# r19 — local installation, actual use and FieldBound capture premise

## Parent and boundary

Goal: continue the unchanged `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` theorem and research compiler. Original source/native domain and quantifiers stay intact. Parent remains OPEN; original conditions closed **0**.

R18 is closed at commit `d51baa6db`. Its reviewed/tested research-only path establishes one source’s Phase-S `FieldBoundV1` receipt through the exact response closure/environment, raw continuation return, distinct outer Apply, live handler arm and `Completed(42)`. It does not establish Install/Capture/FreshUse correspondence or the parent negative-formal construction.

## Fixed outcome

Advance the original receive path `Install(g) -> Capture/FreshUse -> actual g()` without treating source-lineage evidence as a native FieldBound consumer.

This sprint has three coordinated lanes:

1. **Constructive premise derivation:** establish the earliest valid point at which the q/m0/FieldBound evidence exists relative to `Install(g)` capture, and whether the unchanged derivation rules can carry it into the exact `FreshUse` maps and that use's own physical edge/drain. Preserve the owner request `c`, distinguish callback realizer `c_outer`, retain all endpoint/context/scope maps, and apply to the original receive obligation. If current rules cannot form the required evidence before capture, identify the exact first missing rule/premise; do not retroactively add it to an already captured Graph.
2. **Independent source falsification:** use constructor and consumer traces to search for sibling-use, delayed-evidence, scope and endpoint counterexamples. Distinguish actual `Install`/capture order, each authentic `FreshUse`, and physical drain. This lane cannot certify the proof or implementation.
3. **Independent runtime lineage slice:** only through the explicit operation-v1 research entry, derive and observe the source path `initializer Catch -> local binding g -> Name resolving to that exact binder/cell -> Apply of g`. Keep R18's continuation Apply, catch-result closure invocation and callback-body Apply distinct. Require the same HIR/candidate, exact closure handle/environment from the installed cell, actual local `g` call, callback request, live outer handler/arm and `Completed(42)`. The source must first succeed with the unchanged solver and emit its existing static receipt. If it does not, freeze the first acceptance boundary; no semantic/source-rule rewrite in this lane. This runtime result does **not** claim FieldBound survived native capture or was consumed by the use.

Success is a reviewed, same-source lineage from installed initializer to exact local-cell use and live runtime completion, plus a constructive resolution or precise falsification of the capture-to-use evidence premise. A new rule proposal, receipt copy, unrelated green example, source-text equality or family/member equality alone is not success. The smallest falsifier is acceptance of a sibling `g` binder/cell/FreshUse's receipt, or a remapped lower/upper/scope aimed at another use.

## Required source and native owners

Read-only dependency owners at baseline:

- `crates/yu-solver/src/candidate_source.rs`: `operation_v1_catch_source`, source Action production/order.
- `crates/yu-solver/src/candidate_scheme.rs`: `Graph`, `Capture`, `Install`, `prepare_candidate_fresh_use`, `FreshUse` maps, and `begin_candidate_fresh_bound`.
- `crates/yu-solver/src/candidate_effect.rs`: `FieldBoundV1`, native endpoints, q/m0 creation and FreshUse physical edge path.
- `crates/yu-solver/src/candidate_context.rs`: authentic FreshUse admission, evidence import and physical emission/readback.
- `crates/yu-solver/src/candidate_call.rs`, `candidate_intrusion.rs`, `shadow_apply.rs`: use-site routing and public observations.
- R18 runtime files and `notes/design/2026-10-18-operation-v1-source-completion-and-consumer-r6.md`.

The inspected baseline already has generic row/view/context/scope/evidence remapping and authentic FreshUse admission/emission. It does not show q/m0/FieldBoundV1 payload in captured `Graph` or a use-specific FieldBound consumer. Source Action production appends FieldBoundV1 after ordinary source actions, including local uses. These are hypotheses to verify from pinned constructors and actual owner flow, not permission to change solver code in this sprint.

## Exact assignments and write leases

**Constructive proof lane — Sol/high, 720 seconds, Astra 0**

- Write only `notes/theory/2026-10-18-fieldbound-capture-order-and-consumer.md` and `tasks/agent-loop/inbox/20261018-fieldbound-capture-order-and-consumer.md`.
- Construct from the existing source/action/Graph/FreshUse/native consumers. Prove the transport invariant if possible; otherwise freeze the earliest exact missing constructor/consumer premise and its parent application. No code or tests.

**Independent falsification lane — Sol researcher, 360 seconds**

- Write only `notes/theory/2026-10-18-fieldbound-freshuse-source-falsifier.md` and `tasks/agent-loop/inbox/20261018-fieldbound-freshuse-source-falsifier.md`.
- Trace actual owner constructors, scheduled actions, two uses, remapped endpoint/context identities and physical consumer. Seek a concrete source-derived sibling-use or timing counterexample; test injection and type/family equality do not count. No code, tests or builds.

**Runtime implementation lane — Luna/high, 600 seconds**

- Write only `tools/inference-playground/src/runtime/program.rs`, `tools/inference-playground/src/runtime/machine.rs`, `tools/inference-playground/tests/runtime_resume.rs`, and `tasks/agent-loop/inbox/20261018-operation-v1-local-binding-runtime.md`.
- Reuse existing R18 static receipt and research entry. Add fail-closed source-derived initializer-Catch -> binder `g` -> resolved Name/cell -> actual `g` Apply identities and exact runtime handle/environment/owner trace. Preserve ordinary/scoped defaults, `local_grant`, all R18 gates and existing tests. Do not modify the solver or public receipt schema. Freeze before checks; no tests/build/formatter before independent review.

**Independent review — 480 seconds total, split 240 proof/source and 240 runtime code**

- Fresh `spec_auditor` reviews the frozen constructive proof and falsification artifacts; author cannot review either.
- Fresh `compiler_referee` reviews the frozen runtime diff against R18 and this contract; author cannot review it.
- A reviewer finding is not repaired by weakening the source or the original theorem.

**Focused verification/integration — 240 seconds**

After required reviews are CLEAN, Luna may run only:

```text
cargo test -p yu-playground --test runtime_resume
```

The same target must include the new actual-g lineage and a sibling-binder/cell negative control. If unchanged static candidate acceptance fails, record that first boundary; this runtime result remains NOT_RUN/failed and does not change the proof lane result. No solver code tests are authorized because solver files are read-only in this sprint.

Total r19 cap **2400 seconds**, fully conservatively charged when issued; Astra **0**. No carryover or automatic renewal.

## Baseline pins

Git baseline is integrated `d51baa6db` on `research/simple-sub-intrusion` plus the exact committed R18 workspace bytes. Current static-state snapshot and required direct dependencies:

```text
70cff68092ab9af98f5f9a9f4fd16ab3da7d68b19c1c768c8ef131ec55b73a6d tasks/agent-loop/current.json
5341dade52e58e69436c47d9e8fad2bd0cc37d27d6b5c790c8ad8e7f233b6f8f tasks/agent-loop/sprints/operation-v1-runtime-evidence-and-callback-resume-20261018-r18-closeout.md
276979eccec49396c6799b96ca1e0277c6108dc2fd1fe487a52e4565cff6ed54 notes/design/2026-10-18-operation-v1-source-completion-and-consumer-r6.md
0f13f02ad058c8b74b7c4f907a1b9b1fc89345b8c5498707f9c253f2455e3ceb notes/theory/2026-10-18-operation-v1-runtime-resume-correspondence.md
03b44d0f8280c1ae79f66b5528f1bd0b0ffebac46b312ef7ffce605f702f48dd crates/yu-solver/src/candidate_scheme.rs
6112343b4014c67dcb7d814a46412b3af3e1d12183924e891df4817a59f58da0 crates/yu-solver/src/candidate_effect.rs
66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c crates/yu-solver/src/candidate_source.rs
42f89dcf5fa6d7095db1e220c89308a2a35f4e74b05c3e8821d4fb2e3e32b0ca crates/yu-solver/src/candidate_context.rs
e038ad0dfc4b12bd0d513d6cd6b34cee6b2b062d8b33368bc1c0dcdef980d479 crates/yu-solver/src/candidate_call.rs
7a57a93481095c6e7d4b8781810b1a5aa0d174e41ede29ac3f2b2b96bce10b0c crates/yu-solver/src/candidate_intrusion.rs
5bbcf27d51906814ba38b2cca2066807d285d0b1817f0ea6e04d70c4a5c8a5cb crates/yu-solver/src/shadow_apply.rs
7c3e163c5ad710f1eb7f44ab21018fe2788f7334390f1afe6f432d8212f3f34a crates/yu-solver/tests/candidate_operation_catch.rs
bdf996d0264e252e345c05bc77b2adcf625120281244171f0054f1d87a8d1e1b tools/inference-playground/src/lib.rs
d33b61740c256c18664450e909301d19a41c33e568523f648428e329a0bf7e11 tools/inference-playground/src/runtime/program.rs
ef3cba5f89789e393e31ceeb7175f1ca1be6f250f71a150001f9b9fd6ba56f19 tools/inference-playground/src/runtime/machine.rs
194e925c2e19816e05e8d0cdf773123f205dce47d36d83a70385daa07a77e2b3 tools/inference-playground/src/runtime/continuation.rs
459e53b822ac37d260970c94d7dc1b0287085117fa2203fbbc21da5ebfd367f9 tools/inference-playground/tests/runtime_resume.rs
```

## Stop conditions and parent application

Stop a lane at its exact resource cap, frozen output, dependency/hash drift, unsupported or ambiguous source identity, source-language rule requiring a new semantic choice, or first falsifier. No worker expands leases, creates a second team, or changes the source domain. Keep source and native identities distinct; a static HIR occurrence is not a dynamic cell/event/use ID.

Before: one same-HIR direct callback example has a reviewed and green research runtime path, but the original Install/Capture/FreshUse obligation has no q/m0 transport/consumer derivation. After: either a reviewed same-source local-g runtime lineage plus a proved smaller capture/use premise, or an exact counterexample/earliest obstruction with the precise missing source/native owner. Original parent condition closure remains **0 unless independently proved**. Applying any partial result to the original receive obligation and proposing the next critical path belongs to Luna after fresh independent review.
