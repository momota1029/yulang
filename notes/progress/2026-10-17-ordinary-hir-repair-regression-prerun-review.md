# Regression pre-run review: ordinary HIR repair rev5

Fresh read-only reviewer `/root/ordinary_hir_repair_regression_prerun_review`
(`regression_auditor`; requested gpt-6.1-sol/low; observed model/effort
UNKNOWN) STOPPED CLEAN. Exact elapsed unavailable; conservatively charge full
120s. Static inspection only: no writes, Git, Cargo, builds, tests, probes,
network or descendants.

Exact pins matched: rev5 sprint contract
`5c63c3829cd6275523b1799e0286837518e9fd7dd0213c13f3171d9d7b7a6125`, six code/
test pins in shared handoff revision10, and four Cargo root/member manifest and
lock pins.

The focused HIR unit command structurally selects eight `#[test]` functions in
`module.rs`'s `#[cfg(test)]` module, including the required root-collision,
final-classification and 64-indexed-finalization tests. No ignore attributes or
extra feature gates hide them. The HIR integration target has nine tests,
covering exact parse-owned keys, diagnostic order/dense final IDs, punctuation
refusal, causal recovery and final-tree grouped/unresolved error lists. The
solver vertical has one feature-gated `CandidateInference` test and does not
establish standard Apply/Group solving; `ConstraintBatch` still returns Error
and retains `ApplicationTypingRuleUnresolved`.

Command order/caps are CLEAN: focused unit45s, HIR integration120s, solver
integration120s, exact-once. Timeout, compile failure, missing falsifiers or
assertion failure stops without retry, filter substitution or expectation edits.
Post-run independent review remains required.

Limits: no runtime discovery or assertions were executed. The tests check error
kinds/IDs and final-tree attachment, not every rendered diagnostic or
DiagnosticId sequence. Historical before/after assertion preservation was not
exhaustively certified because baseline bytes/Git were out of scope. Original
theorem conditions closed: 0; parent gates OPEN.
