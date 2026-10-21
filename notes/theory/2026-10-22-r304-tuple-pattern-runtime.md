# R304 — ordered tuple case-pattern execution

Status: local implementation RESULT, solo primary, unreviewed. Parent R149 unchanged Types+Console and proof goal remain OPEN.
Baseline: `6e7e5267e954b0211236ce2eabed819d216813c6`; predecessor: R303 tuple source/candidate carryover.

## Governing material and boundary

Re-read the converted unified design §§4.3–4.5, 5.1, 6, 9–10, the proof companion §4.5 and §§7.1–7.5, and the R272 ordered-tuple runtime checkpoint. The R272 machine already stores each evaluated tuple component as a `TupleElement` carrying its received value and view, and preserves source order through prefix/resume. R304 must reuse those exact element receipts. It must not rebuild views, evaluate components again, reorder them, or infer a new effect.

R303's source and candidate paths are held as explicit carryover. Ordinary playground compilation exposed a concrete missing consumer: `runtime/program.rs` exhaustively lowers Integer/Binder/Wildcard only, while runtime Case matching also lacks Tuple. This packet adds exact runtime/program and CLI test leases. It makes no `yu-syntax` or operator-meaning change.

## Source-to-candidate bridge

R303 carryover adds flat tuple binder/wildcard source patterns, ordered negative tuple constraints, and component-row routing. This iteration adds a checked HIR query that verifies `(SourceRootId, case HirOccurrenceId, arm local slot, pattern SourceNodeKey)` identifies that exact parse-owned tuple arm. Candidate admission rejects a mismatched owner, case, slot, or source key before constructing the tuple constraint. Per-arm slots prevent two tuple patterns within one case from sharing the same `ConstraintOccurrenceId`.

The focused source test passes, including rejection of an owned but non-pattern case expression key. The focused solver test passes with two same-arity tuple arms, wildcard projection, swapped component-row identity, and tuple arity mismatch. All 157 `yu-hir` library tests passed.

## Runtime implementation and evidence

`runtime/program.rs` now lowers tuple pattern positions in order, retaining binders and wildcard slots. `machine.rs` matches only tuple values of exactly the pattern arity. Each named component binds the existing `TupleElement.received` value, preserving its view; wildcard slots bind nothing. No component is reevaluated or reordered, and no new effect is introduced. If no arm matches, the existing `NonExhaustiveCase` path remains in force.

The ordinary CLI regression passes. It uses reversed component use to expose order errors, a wildcard component, and wrong-arity/non-tuple scrutinees to exercise mismatch behavior. The HIR test verifies exact source-root/case/arm/pattern ownership and fail-closed duplicate binders. The focused solver test covers two same-arity arms, swapped component identity, wildcard projection and arity mismatch. `cargo test -p yu-hir --features shadow --lib` passes all 157 tests; `cargo test -p yu-solver --features shadow-apply-candidate tuple_case_pattern_projects_binders_through_ordered_tuple_bounds --lib -- --nocapture` passes; `cargo check -p yu-playground` passes; and `cargo test -p yu-playground --test cli_case_source_progress` passes both tests.

The CLI run also exposed that the stdin sentinel `-` was forwarded as a literal module path, breaking source-module projection before evaluation. `main.rs` and the public `prepare` entrypoint now normalize that sentinel to `stdin.yu`. The two ordinary CLI cases pass with this correction. This entrypoint repair is local integration evidence, not a broader import or module-publication result.

## Parent status

These changes do not type or execute the unchanged Yulang2 Types/Console samples. `Display.say` still needs authenticated operator value identity; member schemes, settled receiver readiness, body inference, complete imports/host execution, full tuple publication, source/native correspondence, A/B obligations, independent review, principality and termination remain open. The proof companion's Capture replacement conditions require the full dependency and observation boundary; these local HIR, solver and runtime checks do not establish that boundary or close any theorem gate. R149 remains OPEN.
