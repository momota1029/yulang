# Executable Int and Unit Value formal annotations

Date: 2026-10-10
Branch: `research/simple-sub-intrusion`
Baseline: `f3a5a7e50bed3dedb45c822301bc67564f97423c`
Status: bounded primitive source slice verified and independently reviewed
Authority: [source-confirmed gate](2026-10-10-annotated-value-formal-integration-gate.md),
charter §21 and selected annotation integration policy
Mode: M2; semantic and source/test conformance review; fresh narrow test delta
Measurement consumed: zero timing samples / zero benchmark processes

## Real source and consumer integration

Grouped `(x:int)` and `(x:())` annotations now survive top-level and local
named-function formation. Their identifier source, parameter identity and actual
annotation node stay distinct. Existing annotation parsing supplies its source
owner and depth/recovery validation. Default non-LocalSource lowering is unchanged.
Local whole-binding annotation refusal now checks that owner specifically,
rather than rejecting every descendant formal annotation.

The actual source schedule emits both ordinary value relations before the body:

```text
annotation_positive <= formal_row_negative
formal_row_positive <= annotation_negative
```

The positive edge supplies body/result information without waiting for an actual
argument. The negative edge checks actual arguments, including ignored formals.
Body Names and the Function's ordinary inferred domain use the same actual
formal row in this primitive case. Normal Value entry effects remain; lookup
and lambda construction stay pure. No body-usage rule, early SAT requirement,
non-generic workaround, new grant or skipped constraint is introduced.

Primitive preparation precedes sealing, counters include both facts, and normal
source levels, admission/provenance, graph transport and transaction rollback
own the relations. Cost is one retained actual annotation and two value facts
per annotated primitive formal, linear in source formals. Inline/heap carrier
and action storage are accounted by the existing resource owners.

## Verification and review

Initial independent semantic review found no implementation defect. Conformance
review found that matching literal actuals could themselves supply the asserted
result types. Primary also accepted that global graph leaf searches did not
identify the result fiber. A fresh test-only repair added annotation-only Int/
Unit source, with no literals or Calls, and rooted incoming-Value traversal of
the actual Function result port. Wrong primitives and Function lowers are
excluded. Fresh independent delta review closed the coverage defect without
findings. Original tests/expectations are preserved.

Primary checks use `RUSTC_WRAPPER= timeout 180`, `-j 2 --offline`; tests use
`-- --test-threads=1`:

- `cargo test -p yu-hir --features shadow --lib annotated_primitive_formals`: 1 pass; actual identifier/annotation positions and local/top-level ownership.
- `cargo test -p yu-solver --features shadow-f5,shadow-apply-candidate --test candidate_annotated_primitive_formals`: 7 pass; annotation-only body/export inference, top/local aliases and fresh rows, correct/wrong/ignored/multiple arguments, effectful actuals and explicit unsupported controls.
- Same solver features with `--lib primitive_formal_first_edge_failure`: 1 pass; comprehensive checkpoint rollback/retry, provenance and initial publication failure.

Nine distinct new owning regressions. Initial HIR test compilation failed on a
private re-exported helper path; the primary corrected the test-only import to
the existing crate helper. No production behavior or assertion changed. Initial
three integration tests passed but were insufficient for the reviewed inference
claim; the repaired seven-test run provides the listed stronger evidence.

At the coherent phase boundary, 83 distinct focused tests pass across HIR
annotation positions, primitive formals, source operations, annotations, Unit,
local source retirement, source Value entry, graph Call, intrusion, candidate/
historical lifecycle and preflight inventory/depth. Exact phase commands:

- HIR commands above plus `--lib shadow_annotation_positions`: 9 existing controls.
- Solver integration matrix: `--test candidate_operation_source --test candidate_effect_annotation --test candidate_unit_source --test simple_sub_local_source_retirement --test candidate_lifecycle_retirement --test shadow_apply_candidate --test candidate_value_entry_effect`: 43.
- Solver lib filters: `value_entry_effect_tests` (6, including the one new rollback test), `candidate_intrusion` (5), `candidate_lifecycle_retirement` (7), `candidate_graph_call` (2), `preflight_depth_counts` (2), `candidate_inference_does_not_reserve_historical_call_inventory` (1).
- New solver integration above: 7. New HIR test above: 1. Counts exclude repeated pilots.
- `cargo check -p yu-hir -p yu-solver --all-targets --all-features`: pass.
- `cargo check --workspace --all-features`: pass.
- `cargo check -p yu-hir -p yu-solver`: pass.

No warnings were observed. No broad runtime/resource suite, AST/direct-CST parity
claim, benchmark or full semantic proof is supplied by these focused checks.
Record-only closure edits do not rerun those builds.

## Full objective remains active

Function, variable, computation/effect-bearing formal annotations remain
explicitly unavailable in this primitive slice; this is an incomplete
implementation boundary, not a permanent source restriction or task completion.
The full next constructor must expose the source-owned negative interface while
retaining body-derived shared symbolic closure. Incoming actual callbacks must
not bypass their annotation head through the raw body formal. A proposed always
source-owned interface replaces Oracle's calledness/observed-wildcard selection;
its executable effect/head/residual and contextual transport correspondence
still need integration and independent review. Omitted Function effect ports
also need their exact open-tail and shared-flow construction, not blind reuse
of closed-empty defaults.

Complete Call, effect hygiene, soundness/principality, independently owned public
schemes/default entrypoint and target `yulang3` replacement remain required.
Historical Call inventory withdrawal is a separate coherent retirement, not a
claim that all legacy/public/default owners are gone.
