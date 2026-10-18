# Frozen r18 runtime repair handoff

- Sprint: `operation-v1-runtime-evidence-and-callback-resume-20261018-r18`, revision 3; contract SHA-256 `89483fc7e0e9fc69bb9a7863001012c53e78664d92629d34130bd904f91a4e06`.
- Assignment ID: `r18-runtime-resume-implementation`, handoff revision 2.
- Parent: `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`; original scope and quantifiers preserved; parent OPEN, closure 0.
- Role/worker/session: `/root/r18_runtime_implementation`, implementation lane, current session. Requested model/effort Luna/high; observed model/effort UNKNOWN/UNKNOWN.
- Exact write lease used: `tools/inference-playground/src/runtime/program.rs`, `tools/inference-playground/src/runtime/machine.rs`, `tools/inference-playground/tests/runtime_resume.rs`, and this handoff. `lib.rs` and `runtime/continuation.rs` were read-only and unchanged. No scratch/generated paths.
- Outcome class: implementation candidate, pending fresh independent delta review and gated runtime execution. No theorem or production claim.

## Repair and correspondence

The r1 review blocker was that the machine compared the source site of the actual closure call against `continuation_apply`, which denotes the different inner `k response` Apply. The resulting witness could not be set on the intended execution.

The runtime plan now retains three distinct identities. `continuation_apply` remains the handler arm's `k response` Apply. `response_invocation_apply` is derived uniquely in the same retained HIR/code from the exact matched catch node whose arm links that continuation binder to the exact response definition; it is the unique Apply whose callee subtree contains that catch result. `callback_apply` remains the Apply inside the response closure body that issues the callback operation. The constructor rejects missing, ambiguous or aliased continuation/response-invocation/callback Apply identities.

At runtime, `ResumeArgument` still records the exact response-definition cell read, closure handle and executable captured environment only for the recovered `continuation_apply`. The applied-response witness is now set only at the recovered `response_invocation_apply`, when its callee handle equals that returned closure handle and its executable environment equals the retained captured environment; it also records the newly entered invocation owner. Callback operation evidence and its request event must carry that same owner, alongside the exact callback operation-use, Apply/event, `local_grant`, live outer handler/arm and `Completed(Integer("42"))` gates. Both narrowly guarded function-response paths and ordinary/scoped defaults are unchanged.

The public runtime receipt schema lives in frozen/read-only `lib.rs`, so the new response-invocation site is retained and checked in the private runtime plan/trace, while the existing receipt schema continues to expose its previously leased source fields. Receipt publication is still gated on that exact private site witness.

Added a negative control whose handler arm invokes the same `response` closure at a different Apply site (`response 0`), returns that closure from the arm, and retains the static `k response` arm as the alternate branch. The exact catch-result Apply therefore cannot be attributed to a closure returned through `ResumeArgument`; the research entry must withhold the receipt even if that same closure executes at another Apply. This control was added but not executed.

## Evidence, limits and next step

- Reused the frozen r1 implementation candidate and its hashes below. The fresh integrated review finding was specific: `continuation_apply` is the inner `k response`, not the surrounding Apply that receives the returned closure. No solver, source syntax or semantic rule was changed.
- Checks/builds/formatters: **not run**, as required before fresh delta review. The negative control is unexecuted. No runtime completion is claimed.
- First unresolved acceptance/runtime premise: after CLEAN independent review, the focused run must establish that the same-HIR candidate accepts this source and that actual `local_grant` permits the request/handler path; only then can the dynamic `Completed(42)` receipt be observed.
- Resource allocation: 360 seconds implementation reservation, conservatively charged in full. Actual elapsed/CPU/RSS/tokens UNKNOWN. Astra 0. Parent's total r18 allocation remains 3900 seconds charged; this assignment requests no extension.
- Independent review: NOT RUN by this author; author does not self-review. Next step is Luna's fresh delta review of these exact hashes. Focused `runtime_resume` execution is authorized only after CLEAN.
- Worker state: STOPPED; writes cease after this freeze. Descendants/unresolved descendant leases: none. No further in-envelope author step before review.

Frozen r1 snapshot and read-only dependency hashes:

```text
472ea2f65946bf815834decf599fd105f20dc0c97fde9711746b8d87c0fea1c4  tasks/agent-loop/sprints/operation-v1-runtime-evidence-and-callback-resume-20261018-r18.md
225d4c59aad72d5731aed0adc97f0dc31adf5931f8a66484366a5b2058bdf07e  tasks/agent-loop/sprints/operation-v1-runtime-evidence-and-callback-resume-20261018-r18-rev2.md
89483fc7e0e9fc69bb9a7863001012c53e78664d92629d34130bd904f91a4e06  tasks/agent-loop/sprints/operation-v1-runtime-evidence-and-callback-resume-20261018-r18-rev3.md
bdf996d0264e252e345c05bc77b2adcf625120281244171f0054f1d87a8d1e1b  tools/inference-playground/src/lib.rs (read-only)
194e925c2e19816e05e8d0cdf773123f205dce47d36d83a70385daa07a77e2b3  tools/inference-playground/src/runtime/continuation.rs (read-only)
b17e267b8d9ffe688b031eb1969e6de8200ffa8ee458f6aa9d54d3f7d2450bc1  tasks/agent-loop/inbox/20261018-operation-v1-runtime-resume-implementation.md (frozen r1 handoff)
```

Frozen r1 code hashes before this repair:

```text
da2a1e74f95664516cb8ba5eafcf53e7386e9b12435da5fef069a965da26845f  tools/inference-playground/src/runtime/program.rs
a477e2eae57f826377d71d0d29cfffa5e6b46ca9c58bdc4b332f174d1a0955ef  tools/inference-playground/src/runtime/machine.rs
4fd45306e68bc3665a38644c2369ab2a95e331a40b22ac68a777d1819a3a5cb6  tools/inference-playground/tests/runtime_resume.rs
```

## Frozen repair hashes

```text
095dcb14d6880291b4106b8bce9720e41ed6539b24515baf60ff96abf591ffb5  tools/inference-playground/src/runtime/program.rs
6d438bb26923de7e5d1066d66bdcd071d3fc3b72643f8da3ea966d80e385213d  tools/inference-playground/src/runtime/machine.rs
459e53b822ac37d260970c94d7dc1b0287085117fa2203fbbc21da5ebfd367f9  tools/inference-playground/tests/runtime_resume.rs
```
