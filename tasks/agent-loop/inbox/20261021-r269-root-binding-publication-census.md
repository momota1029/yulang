# R269 handoff — root binding census

- Outcome: reauthenticated the 40-source bundle; temporary Y3 CST probe counted 318 direct-root bindings (313 bodies, five signatures), 258 argument-shaped and 60 no-argument-shaped. The 36 direct `OperatorChain`s are each immediately preceded by an `OperatorHeader`.
- Parent application: publication ownership in current Y3 is located at `crates/yu-hir/src/module.rs` (`plan_root`, `lower_plan`) and `tools/inference-playground/src/runtime/program.rs` (HirItem-to-definition/expression schedule). This is a seam map, not a Y2 correspondence proof.
- Exact unresolved premise: reconcile R260's 307 textual candidates (247 argument, 59 no-argument, one `(mod)`) with 318 CST bindings; identify the 11 extra headers and six additional body-bearing candidates. Y3 CST is not an authentic Y2 parser result.
- Source/native and artifact evidence: 40/40 embedded Git blob IDs verified; focused probe passed and was removed. Results and limitations: `notes/theory/2026-10-21-r269-root-binding-publication-census.md`.
- Next in-scope step: produce exact per-source/range disagreement rows, then trace accepted Y2 module/runtime publication constructors against the current Y3 seam.
- Checks: `cargo test -p yu-playground r269_root_binding_shapes -- --nocapture` passed before temporary test removal. No sample executed; no code/tests retained.
- Writer stop: primary-only packet complete; unreviewed, no retained writer.
