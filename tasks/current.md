# Current task: complete and adopt the successor syntax parser

Updated: 2026-09-08. Branch: `yulang3`; do not modify frozen `main`.

## Objective and current authority

Complete `crates/yu-syntax/src/rewrite/` and replace the old parser through the
existing atomic public/root cutover. Private construction is not that cutover.

- `notes/design/2026-09-08-successor-recovery-authority-amendment.md` is the
  current acceptance/recovery authority. Yulang2 is reference evidence only
  for formally accepted input; choose explicit, reasonable successor recovery.
  The local `grammar/` implementation is older Yulang3, not Yulang2.
- Retain accepted syntax, source ownership, caller/fence boundaries,
  effect-free rejection, truthful typed records, structured reservation and
  emitted extent, and successor fresh/frozen/header-full consistency.
- The user authorizes recovery simplification and recommended design changes,
  documentation/environment maintenance, frequent coherent commits, and
  consideration of generally useful `chasa-recover` shorthand.
- The latest user instruction is direct primary-agent work without subagents.
  Do not restart agent panels merely to continue this task. Deterministic
  verification and honest reporting of review scope remain required.

## Current gate and immediate next action

The shared Call/Parenthesized/EffectRow ordinary-horizontal correction is
complete under the recovery authority amendment §4 and the retained P/E
addenda. Selected P/E/numeric-Call structured Error controls cover exact
records, fresh/frozen reconciliation, shifted origins, native outer closes,
prefix/recursive reservations and outer path continuation. Type tests: 124
passed; output: 4 passed; recovery output: 25 passed; package check passed.

Next: correct the known accepted-Type boundary regressions in declaration
contexts before extending PV recovery. Current direct failures include
`type T = A::with` and `type T = A(B with Inner) with {}`: a contextual word
is returned to the declaration instead of remaining a path segment or nested
Type identifier. Preserve accepted-input tests and fix the owning boundary
decision, not their expectations. This is separate from the completed
horizontal-gap correction. Scope the remaining malformed-only expectations
against current successor authority while doing that review.

The pre-Item scalar-frontier evidence plan is no longer a construction
prerequisite. Its 29 legacy evidence slices remain historical observations;
do not continue that matrix solely to reproduce malformed legacy output. The
reverted primary-completion candidate remains unintegrated; numeric Calls have
the explicit successor rule in the new amendment, and other PV recovery choices
belong to the following current-Item owner gate.

## Following work and residuals

1. Specify and simplify current-Item PV recovery under the new authority, then
   resume the typed-owner migration. Keep one forward pass and no replay or
   scalar observer introduced only for legacy parity.
2. Complete the typed-output owner ledger, actual embedded/header-full proof,
   and remaining public integration gates. T2/T3/T4 local evidence does not
   close aggregate O6 rows. Production Yumark and virtual-context adoption
   remain separate obligations.
3. Resolve the six known `rewrite::tests::type_decl` failures at their owning
   responsibility before broader certification. They predate this delimiter
   candidate (baseline `b85c32f3`) and are not toolchain failures:
   - `type_c12_malformed_path_retry_preserves_caller_stops`;
   - `type_c12_nested_type_owners_preserve_outer_boundaries`;
   - `type_c12_rhs_uses_the_full_ordinary_type_surface`;
   - `type_c15_fresh_type_expression_edges_fence_contextual_words`;
   - `type_c15_keeps_with_outer_only_for_derives_roles`;
   - `type_c15_preserves_header_boundaries_and_nested_suspension`.

## Verification and environment

Use `cargo test -p yu-syntax --lib rewrite::tests::type_expr:: -- --test-threads=1`
for this gate, the focused `rewrite::tests::output::` and
`rewrite::tests::recovery_output::` filters for output/RB invariants, then one
`cargo check -p yu-syntax`. Check inventory before broadening. No benchmark is
needed for the bounded horizontal-gap branch; budget is zero samples/processes.

`cargo xtask check-graph` is the available dependency-direction check, not a
parser test runner. The workspace-local `crates/chasa-recover` already provides
`token`, `maybe`, and `with_str`; do not add generic API for owner-specific CST
or recovery policy. An API addition needs a concrete reusable operation across
independent callers, not just shorter syntax at one site.

## Navigation and history

- Design entry: `notes/design/INDEX.md`.
- Replacement gates: `notes/design/2026-09-02-yu-syntax-recursive-descent-rewrite-plan.md`.
- Typed output: `notes/design/2026-09-06-successor-typed-output-recovery-amendment.md`.
- Current progress: `notes/progress/daily/2026-09-08.md`.
- The former 2,710-line task log is preserved at
  `notes/progress/rewrite-state-before-recovery-authority-2026-09-08.md`.
  Consult it for completed gates, older residual context, and syntax-reference
  site history; it is not an active queue or a source of new authority.
