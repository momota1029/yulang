# Unit primitive integration: implementation and review

Date: 2026-10-10
Baseline: `bbdfd47f5960782743702b3a745fa82b6fa12bb1`
Status: bounded Unit integration verified; full inference objective active
Authority: [confirmed Unit gate](2026-10-10-unit-primitive-integration-gate.md)
Mode: M2 semantic/regression review; measurement budget zero

## Implementation

The actual `yu-types` primitive has positive/negative Unit leaves, indexed and
closed views, finalization, alpha equality and arena branding. HIR retains
explicit Unit and implicit empty-call Unit through ordinary Apply, with distinct
generated occurrence identities at the actual CallTail source key/range.
Whole-binding annotations admit empty type groups as Unit in value/result and
Function argument positions.

Solver endpoints, mismatch shapes, graph capture/freshening/extrusion, native
port validation, summary flags/rollback and primitive result projection retain
Unit directly. Legacy boxed/flat/raw/summary/normalized/replay/closed carriers
have genuine Unit counterparts. Existing Int discriminators and test tokens
are preserved. Source construction prepares Unit leaves before sealing only
where actual Unit values or Unit annotations require them.

Five disjoint producers supplied frozen code; primary integrated the previously
isolated real types delta. No producer performed Cargo or Git integration.
Pre-write `unit_gate_prewrite` confirmed Oracle compatibility and the primitive
`SolvedValue::Unit` correspondence, requiring coherent exhaustive migration.

## Frozen review and causal findings

`unit_frozen_semantics` and `unit_frozen_regression` checked the full 24-path
initial frozen manifest. Accepted findings:

1. Diagnostic buckets still encoded three shape ranks and 45 slots per
   distance. Unit rank 3 causes collisions, wrong distance ordering and an
   actual out-of-range panic. Repair belongs to the shared checked domain
   construction and indexing, preserving the original domain on Unit-free
   inputs. A bounds check would mask the cause.
2. Two existing flat test converters omitted Unit exhaustive arms.
3. New result assertions searched unrelated captured bounds and incorrectly
   required a negative Unit bound at a positive published root. Directed
   body-to-root propagation carries positive lowers forward, not body uppers.
4. The new annotation-only fixture included an empty call, masking missing
   annotation primitive preparation through batch-global literal interning.

Independent pre-write `unit_gate_prewrite` approved corrections to the new
tests: backward lower-bound reachability at the actual root with cycle
protection and no descent into Function arguments for a scalar result;
negative Unit at the actual exposed Function argument and positive Unit at its
result; annotation-only input with no Unit values or Apply expressions.
These correct the tests to the existing contract, rather than weakening
propagation or changing expectations to match observed output.

Fresh `unit_batched_repair` owns the one accepted repair bundle. Initial owning
all-target check reproduced E0004; initial four source tests reproduced three
invalid negative-bound assertions and the diagnostic panic. These failed runs
are retained as causal evidence, not completion evidence.

## Verification already executed

Common Cargo flags: `RUSTC_WRAPPER= timeout 180`, `-j 2 --offline`; tests
`-- --test-threads=1`. Primary runs one Cargo process at a time.

- `cargo test -p yu-types unit_`: 3 passed.
- `cargo test -p yu-types`: 31 unit tests and 32 doctests passed.
- `cargo test -p yu-hir --features shadow --lib unit`: 3 passed.

## Final repair and independent closure

Fresh semantic delta `unit_repair_semantic_delta` confirms that every direct
and external seed contributes to the local diagnostic domain, including losing
seeds. Propagating witnesses retain their kind, so subsequent SCC events cannot
introduce a new rank. Both allocation and indexing use checked
`shape_count * shape_count * 5`; Unit-free SCCs retain the original 45 slots.
No persistent field, additional scan or cache was introduced.

Fresh contract delta `unit_repair_contract_delta` confirms scalar result
reachability, annotation-only Function ports, faithful flat conversions and
boxed/flat closed parity. It then identified two new test compilation defects:
unrepresentable/wrong-type occurrence slots and use of the types crate's
polarity instead of the solver API's polarity. Fresh producer
`unit_test_compile_repair` corrected exactly those three expressions, preserving
assertions; the subsequent narrow contract review closed both findings.
Actual Oracle Git objects were reread directly at the frozen revision, rather
than relying on a missing historical checkout. No outstanding accepted major
or blocking finding remains in this bounded gate.

Final commands use the common flags above. `cargo check -p yu-solver
--all-targets --all-features` and `cargo check --workspace` pass without
warnings. Final focused test filters:

| Cargo command (before common flags) | Passed |
| --- | ---: |
| `test -p yu-types` | 31 unit + 32 doc |
| `test -p yu-hir --features shadow --lib unit` | 3 |
| `test -p yu-hir --features shadow --lib module::source_annotation::tests` | 2 |
| `test -p yu-solver --features shadow-apply-candidate --lib unit_` | 5 |
| `test -p yu-solver --features shadow-apply-candidate --test candidate_unit_source` | 4 |
| `test -p yu-solver --features shadow-apply-candidate --test candidate_effect_annotation` | 5 |
| `test -p yu-solver --features shadow-apply-candidate --lib candidate_effect::tests` | 6 |
| `test -p yu-solver --features shadow-apply-candidate --lib candidate_intrusion::tests` | 5 |
| `test -p yu-solver --features shadow-apply-candidate --lib candidate_graph_call_` | 2 |
| `test -p yu-solver --features shadow-apply-candidate --test simple_sub_local_source_retirement` | 5 |
| `test -p yu-solver --features shadow-apply-candidate --test shadow_apply_candidate` | 19 |
| `test -p yu-solver --features shadow-apply-candidate --lib candidate_lifecycle_retirement` | 5 |
| `test -p yu-solver --features shadow-apply-candidate --test candidate_lifecycle_retirement` | 2 |
| `test -p yu-solver --features shadow-apply-candidate --lib f5d_source_identity_boxed_and_flat_candidates_agree` | 1 |
| `test -p yu-solver --features shadow-apply-candidate --lib f5c_shared_closed_child_is_instantiated_once_per_use` | 1 |
| `test -p yu-solver --features shadow-apply-candidate --lib selected_flat_candidate_matches_boxed_q_r_and_normalization_counters` | 1 |
| `test -p yu-solver --features shadow-apply-candidate --lib f5c_flat_replay_matches_boxed_polarity_and_occurrence_order` | 1 |

129 distinct tests pass; one HIR annotation test appears in two filters and
is counted once. Early `yu-types unit_` evidence is included in its later full
31-test run, not counted again. `git diff --check` passes.

The all-feature check additionally exposed a pre-existing ambiguous test-only
`collect()` in `research_function_realization.rs`. Its explicit expected
HashSet type preserves the assertion and is integrated in a separate M0 commit;
it is not mixed into this Unit change.

No benchmark, exhaustive solver/backend suite or semantic theorem ran.
Measurement consumption: zero samples/processes. Source diagnostic spans and a
separate Unit-bearing closed incoming-use replay are not independently tested
by this slice. Existing parser-stack residual remains recorded; deep annotation
fixtures still run in dedicated workers. Unit support does not establish
complete Call, operation execution, hygiene proofs, public transformed schemes,
soundness/principality or default F5 cutover.
