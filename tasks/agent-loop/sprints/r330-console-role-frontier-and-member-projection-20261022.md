# Sprint R330 — authenticated role frontier through Console member projection

## Parent

The unchanged Yulang2 playground samples must work through ordinary inference and execution, with implementation and source/native proof. Keep the original sample source, accepted effect semantics, source identities, and fail-closed behavior for unsupported ambiguity. Solo primary; no worker or reviewer lane is available in this session.

## Starting evidence

R329 established the Add result reaches the imported `std::io::console.say` FreshUse receiver as positive Int. A focused Console trace showed receiver row 89 and the exact Display subject row 90 each receive the same four Int lower atoms; each has exactly the reciprocal direct upper edge to the other. The source role identity is `std::core::fmt::Display`, and the subject and FieldTail receiver map through the same imported FreshUse. The old frontier walker follows positive lower edges and reports the receiver-to-subject edge as one negative row edge.

R330 adds a narrow provisional readback gate for that exact isolated reciprocal role-subject edge. The selected `show` readback is one exact `Int` implementation. The source owner resolver accepts distinct authenticated HIR projections of one module and continues to reject repeated identical artifacts. Runtime carries exact operator use-site identity for shared providers, falls back to a template FieldTail selection only when all matching source-owned templates choose the same exact member, and resolves both pinned host-write import spellings against the same export identity.

The unchanged Console test now executes through the ordinary module schedule and returns exactly `hello from Yulang\n3\n`. The unchanged Types host-write capture and one-shot continuation tests pass. The complete `cargo test -p yu-playground` package suite passed: 45 library tests plus all listed integration groups. This does not close the stability or source/native proof.

## Goal and falsifiers

1. Prove the role-subject exception is stable for the active source schedule and every later consumer, without collapsing distinct rows or accepting extra upper edges, negative atoms, incomplete inventories, multiple role subjects, or unequal shapes. Otherwise revert the exception and preserve the exact counterexample.
2. Trace and repair the selected `int.show` projection so its HIR definitions and imported uses share a valid collection artifact. Do not bypass SCC endpoint validation or drop source member bodies.
3. **Done for R330:** run the unchanged Console source through the ordinary playground CLI and observe exactly `hello from Yulang\n3\n`; run the package regression groups.
4. Apply the stability argument to the original source/native obligations and record all still-open A/B, all-sample, R149, theorem, review, and production gates.

## Exact ownership

Primary-only leases: `crates/yu-hir/src/module.rs`, `crates/yu-hir/src/shadow.rs`, `crates/yu-solver/src/candidate_scheme.rs`, `crates/yu-solver/src/candidate_source.rs`, `crates/yu-solver/src/lib.rs`, `crates/yu-solver/src/shadow_apply.rs`, `crates/yu-solver/src/scc.rs`, `tools/inference-playground/src/lib.rs`, `tools/inference-playground/src/main.rs`, `tools/inference-playground/tests/cli.rs`, `notes/theory/2026-10-22-r330-console-role-frontier.md`, this contract, and `tasks/agent-loop/current.json`. R327's frozen `module.rs` snapshot is historical; R330 reopens the file for a separate artifact-union API. No other writer is active.

## Resources and stop conditions

2400 seconds, no carryover. Preserve the original source/native gates. If the exact reciprocal-edge proof fails, revert its selector permission and continue with an alternative representation. If projection collection cannot be repaired without weakening artifact or SCC checks, record the exact source owner and next evidence rather than masking the failure. No production promotion from tests or this conditional lemma.
