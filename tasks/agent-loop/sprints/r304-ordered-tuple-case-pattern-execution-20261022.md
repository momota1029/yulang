# Sprint R304 — ordered tuple case-pattern execution

Status: RESULT, local implementation outcome complete; solo Luna primary, no independent review or theorem closure.
Branch / inspected HEAD: `research/simple-sub-intrusion` / `6e7e5267e954b0211236ce2eabed819d216813c6`.
Parent: R149 unchanged 142-byte Types and 92-byte Console samples, original pinned Yulang2 library closure and source/native proof. Parent remains OPEN.
Decision: dispatcher lane unavailable under the user's explicit solo instruction; Luna selected this action from the concrete workspace compile failure below. This is a new exact-lease boundary after R303's next-boundary rule.

## Entry evidence and immediate outcome

R303 added source-keyed flat tuple binder/wildcard patterns and candidate negative-tuple projection. Its focused HIR/solver checks pass. A real `cargo test -p yu-playground --lib unchanged_types_sample_reaches_deferred_field_tail_boundary` currently fails to compile because `runtime/program.rs` has no `LocalSourceCasePattern::Tuple` lowering. Runtime `CasePattern` and `machine.rs` also only match integer/binder/wildcard forms. This makes the preceding local source/solver change unusable by the ordinary playground crate until runtime construction and consumption are connected.

Immediate goal: compile flat tuple case patterns into ordered runtime patterns; match only tuple values of equal arity; bind each named pattern component to the exact corresponding `TupleElement.received` value/view, preserving source order; let wildcard components bind nothing; retain existing first-matching-arm and NonExhaustiveCase behavior. Preserve tuple evaluation and received views already established by R272. Keep non-tuple patterns and other runtime behavior intact.

## Required evidence and falsifiers

Run `cargo test -p yu-playground --test cli_case_source_progress` after adding an unchanged-source CLI case that receives a tuple, projects/reverses binders, exercises wildcard and distinguishes wrong arity/non-tuple values. Verify the returned printed value and ordinary stderr/exit behavior. Run the HIR tuple source test, focused solver tuple test, and `cargo check -p yu-playground`. These implementation checks are not a source/native theorem.

Falsify order with `(first, second)` used in reversed output; falsify binder transport with values whose `ReceivedValue` views are distinguishable where the existing test harness permits; falsify arity with a two-pattern against one- and three-element tuple values; falsify wildcard by using an otherwise unconstrained component. A nested, recovered, or duplicate-binder tuple pattern must continue to fail closed at source formation. Record unsupported residuals instead of rewriting samples.

## Outcome

The exact-arity runtime tuple matcher and ordered binder projection are implemented. The source/HIR, focused solver, normal playground build and CLI evidence listed in `notes/theory/2026-10-22-r304-tuple-pattern-runtime.md` passed. The stdin sentinel is normalized at both CLI and library entrypoints after the ordinary CLI exposed the module-path failure. No `yu-syntax` or operator semantics changed. This is a solo implementation result, not a reviewed theorem, source/native proof, or completion of R149. The unchanged Types/Console sample boundary and the operator-value/member-candidate path remain open.

## Proof correspondence

Trace `LocalSourceCasePattern::Tuple` source key + arm ordinal through candidate recipe and admission: the exact parsed HIR root, case occurrence, arm slot and pattern key must agree before the negative ordered tuple constraint is admitted. Then trace tuple runtime construction (`TupleElement` retains each received value and view) and case matching/binder projection. The runtime pattern performs no additional evaluation, reordering, view reconstruction or effect action. Apply any local preservation argument to the original source/runtime step and keep the source/native, A/B, principality, termination, Console and production gates OPEN.

## Exact leases and resources

Exact leases: `crates/yu-hir/src/module.rs`, `crates/yu-hir/src/module/local_source.rs`, `crates/yu-hir/src/shadow.rs`, `crates/yu-solver/src/candidate_source.rs`, `crates/yu-solver/src/candidate_value_graph.rs`, `crates/yu-solver/src/shadow_apply.rs`, `tools/inference-playground/src/runtime/program.rs`, `tools/inference-playground/src/runtime/machine.rs`, `tools/inference-playground/src/main.rs`, `tools/inference-playground/src/lib.rs`, `tools/inference-playground/tests/cli_case_source_progress.rs`, `notes/theory/2026-10-22-r303-role-member-candidate-typing.md`, `notes/theory/2026-10-22-r304-tuple-pattern-runtime.md`, this contract, and Luna-owned `tasks/agent-loop/current.json`.

One serial primary process at a time, 3600-second cap, no carryover, no background work, no subagents. No `yu-syntax` changes or operator semantic expansion in this packet. Unknown legacy workers remain UNKNOWN with quarantined ownership; do not reclaim them. Only Luna integrates and pushes. STOP/session end leaves the primary WAITING or UNKNOWN according to actual write cessation.

## Parent application and remaining work

This packet repairs the compile/runtime seam created by the previous tuple-pattern source and candidate support. It does not make the Yulang2 samples type or execute end to end. `Display.say` still needs an authenticated operator value path, member candidate schemes and receiver readiness; Types and Console remain blocked; complete ordered Tuple inference/publication/runtime and source/native proof remain open. No theorem gate closes from these tests. R303/R304 evidence remains solo and unreviewed; R149 remains OPEN.
