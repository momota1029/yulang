# R327 — Console operator result to consumer FieldTail

## Baseline and correction

R326 commit `483d26976` is pushed. It adds whole-module Console runtime scheduling, exact local/imported `out::write` source identity, and local-name shadowing of implicit-prelude lookup. The exact unchanged 92-byte Console source passes provider projection and operation preflight, but candidate inference still returns `Solve(DeferredSelectionUnavailable)` rather than `hello from Yulang\n3\n`.

The user's effect-row correction remains binding: contravariant `[io]` means open `[io,'e]`, so `[state]` is permitted. R327 makes no effect-row closure or narrowing claim.

## Exact evidence

The Console trace maps the top-level `say` Apply argument to the result row of `1 + 2`. At operator occurrence 5, both operands have shape `Int`, while the result row is unshaped. The same unshaped row reaches the argument of the `say` Apply. This does not establish a broken Apply-to-FreshUse row map; the missing shape first appears at the operator result.

Before selection, the FieldTail receiver readbacks include an `Int` receiver for the `Add` role with a unique `int` target, complete implementation inventory, no unsupported targets, complete positive frontier, empty negative frontier, and no prerequisites. The corresponding `Str` `Add` readback is also unique. The exact pinned source states `Add 'a` as `a.add: 'a -> 'a`, `int.add` delegates to the imported `std::int::add`, and that binding has type `int -> int -> int`.

`pinned_applicable_member_projection` now projects only the exact source member selected by complete, stable `add` readbacks, and only for a consumer containing `+`. After projection, the `Int` `add` FieldTail is discharged, confirming that the exact `int.add` member is present in the candidate world. The dependent `show` receiver still has no positive shape; its reachable frontier contains one negative row edge and no concrete positive bound. Inference remains fail-closed with `DeferredSelectionUnavailable`.

The full playground run exposed four unrelated Types failures. The selected `Display.say` HIR projection failed because `retain_implicit_prelude_role_ids` scanned every identifier in `fmt.yu`; the unrelated `text` identifier reached a recovered `std::io::file` export and failed closed. The helper now scopes prelude role-ID retention to identifiers in the selected source roots, and source-name collection accepts the nested exact member source key. This preserves the source identity checks while avoiding unrelated file contents.

## Result and next premise

The pre-selection member-source gap is closed for uniquely evidenced Add targets. The Types selected-member import regression is fixed. The expected result-shape propagation from the selected `int.add` body into the operator result and then the `say` FreshUse is **not** established. The next investigation is the polarity and constraint path from the selected member's `int -> int -> int` imported call through the operator graph's result row. Preserve the exact source lineage and do not add equality from unrelated readbacks.

The regression test records both facts: exact Add selection is discharged after projection, while Console's Display `show` selection and overall inference remain deferred. Console execution, `Display.show`, source/native adequacy, R149, all-sample completion, proof closure, review, and production remain open.

## Verification

- Focused `unchanged_console_sample_projects_add_but_keeps_display_selection_deferred`: passed.
- `cargo check -q -p yu-playground`: passed with existing warnings.
- Exact `--run-module` input: still returns `candidate inference unavailable: Solve(DeferredSelectionUnavailable)`.
- `cargo test -q -p yu-playground --lib`: 45 passed, 0 failed after the selected-root prelude fix.
- The R327 2400-second cap was exhausted; work continues in R328 with no carryover.
- Commit/push is still blocked because the execution sandbox mounts `.git` read-only (`git add` cannot create `.git/index.lock`). Source and documentation changes remain in the working tree.
