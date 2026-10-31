# Sprint EFFECT-PERMISSION-STRUCTURAL-BUFFER-BOUND/20261029-r18

Status: admitted by Luna under the unchanged Yulang inference/executor soundness goal after R17 `CLOSED_COMPLETE_CONDITIONAL` and the sprint-end selector's source-grounded obstruction candidate.

## Original parent and fixed question

The original inference/executor soundness, effects, principality and termination obligations remain unchanged and OPEN. This bounded packet addresses a narrower prerequisite: whether the six-slot `TermCapacityEvents` buffer can reach an assertion failure on the existing structural tuple route before `with_term_events` drains it.

Trace the existing route `candidate_formal_value_pair → positive_tuple → intern_tuple → intern_structure → intern/push`. Produce exactly one of:

1. a checked conditional trace in which six events from the selected R16 intern protocol are followed by the structural-owner event, identifying the seventh indexed push and assertion failure; or
2. a source-verified invariant that excludes this simultaneous trace on the selected route.

Every primitive allocation/reserve, capacity-change, page-claim and successful-intern premise must remain explicit. Do not infer native reachability from independent Boolean choices, use an arbitrary seven-element list as a source trace, or conflate successful `try_reserve` return with actual allocation evidence. Distinguish a locally possible arena state from an authenticated candidate-call execution.

## Frozen baseline and exact owners

R17 artifact `notes/theory/lean/YulangClosure/FormalPermissionEventBuffer.lean`, SHA-256 `1886b763ebd493721cd6cb7d03f32ff3c43555587a53ccf4e0ee3c351c450b57`; R17 input manifest SHA-256 `53052f07b01674a05ad9c2511dbe3fb9319ee6922183baf0dd2c27bf520b40ae`; R17 contract SHA-256 `f181371ae07baddbb95be34ae9ba1b7161e8786ddb26ace1d608d92b7e271a47`.

The source lane maps `crates/yu-solver/src/candidate_effect.rs`, `candidate_scheme.rs`, `term.rs`, and `lib.rs`, including route/journal initialization and child validity. It also reads the R17 model and source handoff. Freeze each admitted byte hash in the R18 manifest and source handoff before proof work. No compiler repair lease is granted; all Rust files are read-only.

## Lanes, leases and resource bounds

- One registered `lean_prover`, 600 seconds maximum active work. Write only `notes/theory/lean/YulangClosure/FormalPermissionStructuralBufferBound.lean` and `tasks/agent-loop/inbox/effect-permission-structural-buffer-bound-r18-proof.md`. Use the pinned Lean 4.35.0 project and isolated outputs under `/tmp/yulang-effect-permission-structural-buffer-bound-20261029-r18/`. No descendants.
- Luna primary, up to 200 seconds for read-only source trace and source handoff; write only `tasks/agent-loop/inbox/effect-permission-structural-buffer-bound-r18-source.md` plus central sprint records owned by Luna. No Rust edits.
- After a complete successful primary audit, one fresh nonauthor `compiler_referee`, 250 seconds maximum, read-only review returned by message. It may not alter the artifact or write a review file.
- Luna primary, up to 150 seconds for admission, at most two audits, review adjudication, state synchronization and closeout. No Astra and no descendants beyond the listed reviewer.
- Total sprint envelope: 1,200 seconds. Assign one build/cache owner. At most two separately frozen Lean 4.35.0 audits, each at most 90 seconds and 120 seconds combined; run serially with `-j1`. Audit every public theorem root in R18 and all 73 inherited roots (R12/R13/R15/R16/R17). Preserve full types, transitive axiom reports, stdout/stderr, status, resource and input-copy receipts. No diagnostic third audit.

## Evidence and stop conditions

The handoffs must identify the exact source constructors/callees, array index, bound assertion, all represented and omitted cases, original-parent application, first remaining native premise, actual worker/session/model observations, resource spend, and writes-stopped status. A source-qualified native counterexample requires an authenticated execution path; a conditional Lean witness alone is not such a counterexample.

Stop on a source/input hash drift, path conflict, inherited root failure, budget expiry, drain/interleaving that invalidates the trace, earlier failure preventing the sixth event, source invariant excluding the seventh event, or any unsupported premise. Preserve a conditional result honestly if native reachability remains unproved. Do not revise the original parent, accepted semantics, production authority or source domain.

No tests, Cargo, Rust execution, instrumentation, production edits, package updates, Git staging/commit/push, or changes to R17/earlier artifacts are authorized. Parent/native, hygiene, consumer, soundness, principality, termination and production gates remain OPEN absent their own evidence.
