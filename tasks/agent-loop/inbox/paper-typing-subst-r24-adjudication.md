# R24 primary adjudication — operation-mapper adapter typing

Sprint `FULL-PAPER-TYPE-SUBSTITUTION-20261026/r24`, contract r2 SHA-256
`113e20cc94f1917c7761681037ac6d275a0d68f57f35c920680647ae2a282b80`.
Baseline `c2bd4055094e7b75a2155638611f015f0baa52ea`.

## Disposition

**R24 accepted as a reviewed prerequisite within its bounded scope.** The accepted result is the separate `MapperPlanTyped` evidence for both operation-mapper adapter derivations, exact inversion including witness lists and full instance equalities, same-identity consequence, arbitrary simultaneous type-substitution transport of the actual `mapMapperPlan σ mapper`, and the positive/negative adapter-polarity discriminator.

The result does not add a `PaperComputationTyped.mapOperation` constructor, establish typing for the complete operation-mapper computation rule, prove execution/preservation/freshening, or close the original full-paper parent. The missing rule-to-computation integration is the selected R25 seam. R23's stored-body/caller context blocker and R18's variant type-argument correspondence remain OPEN. Inference/executor, A/B, source/native/Rust and production gates remain OPEN; `NO_SAFE_CODE_SLICE` remains.

## Frozen evidence and review

- Module `notes/theory/lean/YulangClosure/PaperOperationMapperTyping.lean`, SHA-256 `175c307e00bea7ba6ec44ff153f50a7d9d943de8bdc3d4dccb02a41bc53dde77`.
- Worker handoff `tasks/agent-loop/inbox/paper-typing-subst-r24.md`, SHA-256 `7d8393f245adee34ed00fd1de39f2856547a3609485b25319911e93bbc307d7a`.
- Primary build/type/axiom receipt `tasks/agent-loop/inbox/paper-typing-subst-r24-primary-verification.txt`, SHA-256 `8e3064793034725921e91352b01ac320c5335b0b3ea6838ca9aeb72b62db6d8e`.
- Fresh non-author M1 report `tasks/agent-loop/inbox/paper-typing-subst-r24-review.md`, SHA-256 `8829cdde3a8e2f9fe5c56a5d25f619a4578ec2e9842c07b15e3e3313b9c18d3e`; verdict **no blocking or major findings; no material minor finding**. Reviewer ran 0 checker calls and STOPPED.
- Auxiliary audit source `.lake/R24Audit.lean` in `/tmp/yulang-r24-mapop`, SHA-256 `e72f5648afd52e144802c6e1f1f62808ff0693c23a23f80b0580bb88007786d3`; exact hash is recorded in the frozen handoff.

The focused build passed. The exact ordered audit validated 13 complete theorem type/axiom blocks; the relation constructor reported no axioms. New theorems reported: inversion and sameIdentity with no axioms; typeTransport `[propext, Quot.sound]`; positive discriminator `[propext]`; negative discriminator `[propext, Quot.sound]`. All other audited dependencies reported only `[propext, Quot.sound]`. No `sorryAx`, unapproved axiom or failed theorem appeared. `check_lean.validate_audit` passed over the retained primary output. The independent review reconciled source, exact witness equalities, actual mapped-plan result, all 13 theorem reports and the constructor report.

## Resource incident and accounting

The initial Lake command incorrectly put Lean flags at Lake's top level and exited 1 with `error: unknown short option '-j'`; this was a Lake CLI option error before Lean checking, not a theorem/source verdict. R24.1 charged that invocation and reallocated one unused worker call to primary without increasing the fixed total envelope.

Final accounting: **3/8** serial invocations (primary 3/3, proof worker 0, reviewer 0); the three primary calls were the charged CLI error, successful focused build, and successful complete audit. Successful primary process wall intervals were approximately 13.2s and 1.2s; CPU/checker internal time was not separately measured. Total checker budget remains 120s, with about 14.4s observed successful process wall and no reset or carry-forward. Active time was not instrumented. No tests, default build, Rust build, dependencies, network, children or source semantics changes.

## Accepted scope and next seam

The source gate is supported by manuscript `:694–719`, shared `D/Gamma` notation `:203–207`, shared `Xi` convention `:269`, accepted R19 single-formal representation, and the exact operation-instance/declaration instantiation definitions. The proof does not open a new type binder or claim R23 caller-context closure. Both adapters keep one declaration/graph/captured context; source payload maps forward, target response maps backward; complete `argsSyntax` instance equalities are retained.

R25 may investigate the computation-typing integration of the operation-mapper rule under a new fixed contract, with frozen source modules leased explicitly only if the exact proof path requires edits. R24 artifacts remain read-only. The selected target is the omitted `mapOperation` computation typing seam and its arbitrary-substitution case; its paper derivation, exact equivalence/inversion statement, syntax/module import direction and required source authority must be checked before granting any writer lease.
