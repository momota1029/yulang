# Sprint R327 — carry Console arguments into FreshUse FieldTails

Status: ACTIVE, solo serial lane. Baseline: pushed commit `483d26976`. Parent goal remains all unchanged Yulang2 playground samples through ordinary inference/execution, with implementation and source/native proofs.

Authority: original sample bytes and expected output in `notes/design/2026-10-20-r149-types-console.md`; the committed Japanese unified design and proof companion; R327 preserves the correction that a contravariant `[io]` annotation means `[io,'e]`, so a `[state]` contribution is permitted. Do not close or narrow the open row.

## R326 result

Commit `483d26976` is pushed. It adds whole-module Console runtime scheduling, exact local/imported two-segment `out::write` identity, and local-name shadowing of implicit-prelude lookup. Focused source-identity and Console-boundary tests pass. The exact unchanged Console CLI crosses imports and operation preflight but stops at `DeferredSelectionUnavailable`. Console output and source/native proof remain open.

## R327 objective

Trace `say: 1 + 2` from the exact source Apply argument through its instantiated function input to the `value.show` FieldTail receiver in `console.say`. Current exact readbacks show the receiver's authenticated `Display` subject linked only by an upper-bound frontier; the concrete integer shape is absent. Determine the positive/negative row direction from the captured function graph and the FreshUse maps, preserve the original relation provenance, and add a focused invariant test. Do not manufacture equality, infer a shape from unrelated evidence, weaken principality gates, or change effect-row variance.

After the transport is justified, continue the exact Console flow through unique `Display.show`, `int: Add`, selected `int.add` member source, and authenticated host writes. Expected CLI output remains `hello from Yulang\n3\n`. Then continue through every unchanged Yulang2 playground sample and the required proof obligations. Tests are implementation evidence only.

## Constraints and verification

- No agents or background workers. Luna remains sole editor and Git integrator.
- Keep edits within `candidate_scheme.rs`, the R327 note/contract, and current sprint state unless a newly evidenced integration seam requires a revised lease.
- Fail closed on ambiguous/missing/unstable FieldTail selection and unresolved prerequisites.
- R327 cap: 2400 seconds, no carryover. Commit and push coherent progress; inspect the full outbound range before non-forced push.
- Verify with the exact unchanged Console CLI, focused FreshUse/FieldTail tests, `cargo test -p yu-playground --lib`, `cargo check -p yu-playground`, sprint static checks, and `git diff --check` as relevant.
- No source/native adequacy, R149 closure, all-samples completion, independent review, theorem closure, or production claim follows without its own evidence.
