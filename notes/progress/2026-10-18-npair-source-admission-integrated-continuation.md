# NPAIR source-admission integrated continuation

Sprint `npair-source-admission-correspondence-20261018` continues under the
same adopted source slice and parent theorem. The two source-entry attempts
both fail in HIR lowering before solver entry; this continuation carries the
investigation through a repairable producer path or freezes the first owner
obstruction, without changing theorem quantifiers or accepted row semantics.

## Authority and bounds

Dispatcher recommendation adopted by Luna on 2026-10-18. Additional envelope:
1800 seconds (primary 900, constructive proof 300, independent compiler and
spec review 120 each, reserve 360), cumulative sprint cap 4260 seconds. Full
envelope is reserved at issue. Astra 0. One verification owner; initially at
most two Cargo invocations, each capped at 120 seconds. After those were spent
(first: HIR failure; second: test-diagnostic compile error), dispatcher
reallocated reserve: primary180, one final Cargo invocation120, evidence60.
The cumulative cap is unchanged. No broad suite.

Luna owns writes only to `crates/yu-solver/src/candidate_source.rs`, including
the existing bounded candidate predicate and its source regression. One
prover owns the first-failure theory note and inbox. Existing four syntax and
four HIR read paths remain read-only. Any required syntax/HIR change is outside
this continuation and must be frozen as a minimal contract first. No source
semantics expansion, expected-output changes, or parent promotion is allowed.

The exact adopted predicate remains: admit a nonempty concrete-only negative
formal-port row; preserve existing acceptance/refusal for all other shapes.
Target evidence is normal parse -> HIR -> `CandidateInference::solve`, plus
neighboring source refusal checks. The old internal producer test is a fixture
reference, not proof of source-entry success.

## Pinned inputs

| Path | SHA-256 |
| --- | --- |
| `crates/yu-solver/src/candidate_source.rs` | `8d695bd9c71ed8b145456917e973528c1c87c5728073615641cb59f55fdbb2f0` |
| `crates/yu-solver/src/candidate_effect.rs` | `9ea9498692bdff12c2a7ebd8546ca2b443a095c0700f3e87ad6c956cc690e212` |
| `crates/yu-hir/src/module.rs` | `60e91c9a51394b04af42b3ec7c284062b34fcd9faa4ea79c35b4ae58aaf460ed` |
| `crates/yu-hir/src/module/local_source.rs` | `ede8b845e1ad19bb1481d7e6337cefa1f117197512975f0f306dc6edb79672e5` |
| `crates/yu-hir/src/module/source_annotation.rs` | `b8462b66eac24a48b6fc5e931a3d8b7c38c19bb8b2f1a7cdc4ecd9a8a7a1117f` |
| `crates/yu-hir/src/source_identity.rs` | `7f0ba057a28ec8c42d2b08bcbe698ee9b422819bfde8ea43ce184457ea586bb3` |
| `crates/yu-syntax/src/pattern/mod.rs` | `1b608422c93ce0f6947125a9b1ea88314a48b3a5e45030ed23e5154492ad7883` |
| `crates/yu-syntax/src/pattern/delimited.rs` | `9da9ec948775b438a85ca3f27c2805254a4f4171caddb54cabe44e563d017029` |
| `crates/yu-syntax/src/type_expr/mod.rs` | `2e08a49960cd4010ba39641ae509afb7cf59711c1464d3349f5f6db590ebf01f` |
| `crates/yu-syntax/src/type_expr/delimited.rs` | `db6335a8f6c95bafb72d096fe241201202938c5869fb89a5e3c43758021651b6` |

The earlier failure-read lease had a one-character typo in its
`type_expr/mod.rs` digest. The digest in this continuation was checked against
the current file before reading; it supersedes that typo. Current candidate
source working bytes after the final test-helper correction:
`74a83e04a3ecc88a8711ae9ffb2d2bc7274f40eaa2f7eb789ebb0c0980354067`.

The third focused run executed one test. The target nonempty concrete-only
negative row passed the normal HIR and `CandidateInference::solve` path, as did
the formerly admitted neighbors and the empty/mixed-row solver refusals. The
last multiple-symbol source was refused by HIR before solver entry; the test
helper incorrectly unwrapped that expected earlier refusal. Dispatcher
authorized a 300-second bounded continuation from the next sprint envelope:
Luna120, one final Cargo run120, evidence60. The helper now checks that exact
multiple-symbol case for `StructuralProjection`, while keeping the empty and
mixed cases at solver level. New cumulative cap: 4560 seconds, Astra0.

The final exact source-entry test ran one test and passed. It verifies the
adopted nonempty concrete-only negative formal row through ordinary parse,
HIR, source annotation lookup and `CandidateInference::solve`; formerly
admitted neighboring cases remain accepted, empty and mixed rows are refused
by the solver, and the multiple-symbol row is specifically refused at HIR.
This is bounded implementation evidence, not closure of the parent theorem.

Prior failures are preserved in
`notes/progress/2026-10-18-npair-source-admission-second-hir-failure.md`.
Original-condition closure remains 0. The existing candidate source change is
unreviewed and unintegrated until fresh code review and successful targeted
evidence.
