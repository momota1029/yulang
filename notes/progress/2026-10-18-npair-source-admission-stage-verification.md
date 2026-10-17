# NPAIR source-admission stage-specific verification continuation

Sprint `npair-source-admission-correspondence-20261018`; parent
`CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`. Parent closure remains 0;
the adopted row semantics, source domain and all quantifiers are unchanged.

## Review finding and bounded repair

The frozen candidate at SHA `74a83e04a3ecc88a8711ae9ffb2d2bc7274f40eaa2f7eb789ebb0c0980354067`
passed its focused source-entry test. Fresh compiler and spec reviews found no
predicate or scope defect. The compiler review classified one minor evidence
gap; the spec review classified the same gap as a major verification
overclaim. Both found that the
test's `solve_formal(...).is_err()` accepted either a HIR lowering error or a
solver error, so the receipt overclaimed solver-stage refusal for empty/mixed
rows.

Dispatcher recommendation adopted by Luna: 420 seconds, bringing the
cumulative cap from 4560 to 4980 while preserving all prior charge. Allocation:
primary repair90, one focused Cargo run120, independent compiler review60,
independent spec review90, evidence/integration60. Astra0. Write scope remains
only `crates/yu-solver/src/candidate_source.rs`; no HIR/syntax edits or semantic
changes. The repair makes `solve_formal` require successful HIR lowering before
calling the solver; the multiple-symbol case retains its exact HIR refusal
assertion.

Repaired candidate bytes frozen for the one authorized rerun:
`crates/yu-solver/src/candidate_source.rs`, SHA-256
`4ea9d89e4a31e7be4ce170517e50eea31dd9e054c360cedba9ccc9cb7ced69ce`.

## Required evidence

Run the same fully qualified focused test once. It must execute exactly one
test and pass with HIR construction explicit for empty/mixed source rows, then
solver refusal. The adopted nonempty concrete-only negative row must continue
through parse, HIR and `CandidateInference::solve`. The multiple-symbol row is
tested separately and remains refused at HIR. Any failure stops this
continuation; no fixture retry is authorized.

## Result

The exact focused test ran **1 passed, 0 failed**. For empty and mixed rows the
test first unwraps successful `lower_module_with_local_source` and then checks
`CandidateInference::solve` returns refusal. The multiple-symbol input is
checked separately for HIR `StructuralProjection`. The adopted target still
passes parse, HIR, source-annotation identity checks and candidate solve. Final
code SHA remains `4ea9d89e4a31e7be4ce170517e50eea31dd9e054c360cedba9ccc9cb7ced69ce`.
This closes the review finding; parent closure remains 0.

Afterward freeze the new code and this receipt, then obtain fresh independent
compiler and spec delta reviews. The former review receipts apply only to the
previous frozen SHA and their finding is preserved in the preceding final
verification record. No commit or parent promotion occurs before the new
reviews and Luna adjudication.
