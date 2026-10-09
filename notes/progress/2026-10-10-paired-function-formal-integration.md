# Executable paired Function formal interfaces

Date: 2026-10-10
Branch: `research/simple-sub-intrusion`
Source baseline: `2d6cf2570f575c6563cf8e5691b334e6a705e575`
Constructor checkpoint: `1295478faba6c77f04b8ce358ea67006c3d2ae15`
Status: bounded implementation verified; independent runtime and final feature-guard deltas clean
Authority: [source constructor gate](2026-10-10-paired-function-formal-construction-gate.md),
selected annotation policy and Simple-sub legacy withdrawal
Mode: M2, independent semantic and source/test conformance review, fresh repair deltas
Measurement consumed: zero timing samples / zero benchmark processes

## Actual constructor and consumer

Grouped Function and named-variable formals now construct their positive and
negative interfaces together before body inference. Each Function node has two
distinct ordinary inferred effect rows, shared across its two polarities.
Actual callback effects reach body invocation and latent returned callbacks
through these rows. The enclosing Function consumes the retained negative
interface; body Names retain their ordinary formal row. No direct actual-provider
edge to that raw body row bypasses the annotation.

Named value rows are shared by actual defining binding, including the current
top whole-binding annotation. Different locals retain separate environments.
These are ordinary Simple-sub rows permitting union lowers, not rigid annotation
variables. No calledness decision, observed-port reconstruction, early SAT or
registry prerequisite is added. Explicit effect rows and wildcard construction
remain separate unfinished integration work.

Construction is linear in annotation nodes and distinct scoped names. Existing
source levels and the admitted 128-depth syntax envelope apply. Runtime domain
and named-row associations, owned strings and undo entries are accounted and
journaled; ordinary capture/freshening/extrusion/intrusion transport the actual
Function children and rows. No new graph node or second semantic memo is used.

## Owning rollback defect and review closure

The stronger failure/retry witness exposed that `ConstraintStore::rollback_route`
removed only one new canonical fact and receipt. It now removes the complete
new fact suffix and minted receipt interval, preserving old entries and handling
duplicate admissions and unconsumed receipts. Work is proportional to new
admissions on failure, with no whole-store scan or new rollback allocation.

Initial independent reviews accepted the constructor but found the new test's
epoch boundary and missing live-storage sampling. Successful begin advances the
journal epoch; retain it to avoid stale seen-mark collisions. The test captures
inside begin, repeatedly mutates an older shared row, verifies complete logical
restoration and retries. Global checkpoint/generation-exhaustion assertions stay.
Samples precede named/domain failure hooks; private census checks live retained
and undo payloads and surviving diagnostic container capacities after rollback.

Fresh delta reviews and deterministic checks exposed further witness errors:
sigil names include the apostrophe; restored counters cannot be compared with a
stale live-allocation sample; initial whole-session failure has no route journal;
and `FactKey` equality itself changes comparison counters. New witnesses retain
exact assertions with the correct ownership/phase and plain canonical tuples.
The final fresh semantic delta closes the accepted runtime/store/witness findings.
This finite accounting evidence is not a full resource-ledger proof.

Pre-write conformance permits moving only the temporary Function/named-variable
unsupported fixtures into positive source coverage. Explicit effects, patterns,
whole-local annotations and all other historical controls remain.

## Verification

Primary alone runs Cargo, using `RUSTC_WRAPPER= timeout 180`, `-j 2 --offline`;
tests use `-- --test-threads=1`. Solver test features are
`shadow-f5,shadow-apply-candidate` unless explicitly stated otherwise.

- Integration matrix: `cargo test -p yu-solver --features shadow-f5,shadow-apply-candidate --test candidate_annotated_function_formals --test candidate_annotated_primitive_formals --test candidate_operation_source --test candidate_effect_annotation --test candidate_unit_source --test simple_sub_local_source_retirement --test candidate_lifecycle_retirement --test shadow_apply_candidate --test candidate_value_entry_effect`: 55 pass.
- Lib filters: `value_entry_effect_tests` (8), `candidate_effect::tests` (10), `store_route_rollback_removes_all_new_keys_and_receipts` (1), `f5c_incoming_route_generation_exhaustion_is_atomic` (1), `brands_receipts_and_local_failure_are_isolated` (1), `candidate_intrusion` (5), `candidate_lifecycle_retirement` (7), `candidate_graph_call` (2), `preflight_depth_counts` (2), `candidate_inference_does_not_reserve_historical_call_inventory` (1): 38 pass.
- Total: 93 distinct focused tests, including nine new owning regressions. Counts exclude repeated pilots and repair attempts.
- `cargo check -p yu-hir -p yu-solver --all-targets --all-features`: pass.
- `cargo check --workspace --all-features`: pass.

The default owning check found the new domain lookup lacked the existing
`shadow-apply-candidate` field guard. The final repair guards the lookup and
retains the ordinary raw domain when the candidate feature is disabled; the
enabled constructor branch is unchanged. Independent narrow semantic review
closes this delta. Final default-feature commands pass:

- `cargo check -p yu-hir -p yu-solver`.
- `cargo test -p yu-solver --lib store_route_rollback_removes_all_new_keys_and_receipts`: one pass, already included in the distinct-test count above.

Failed pilots are recorded above as defects, not successful evidence.
No warnings were observed in successful checks.
No broad runtime/resource suite, HIR/AST/direct-CST parity suite, benchmark,
backend execution or full semantic proof ran.

## Remaining full objective

Explicit negative `[E]` requires authentic attachment construction, contextual
Value/Effect transport, consumed insertion filters, future lower checks and
head/residual output handling. Wildcards and whole-local annotations remain
missing producers. Source Value entry roles through all whole-binding annotations
still need exact passthrough correspondence. Independently owned public schemes,
a real cross-session importer and ordinary default entrypoint migration remain
required. Complete Call, effect hygiene, soundness/principality and target
`yulang3` replacement are not closed by this private source gate.
