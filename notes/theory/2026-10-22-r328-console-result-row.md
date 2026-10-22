# R328 — trace the Console operator result row

## Baseline

The worktree contains R327 changes on top of pushed commit `483d26976`; `.git` is read-only in this environment, so the current increment cannot be committed or pushed here. R327 reached its 2400-second cap with no carryover.

The R327 implementation projects exact Add member source only when pre-selection receiver readbacks prove a unique target, complete inventory, complete stable positive frontier, empty negative frontier, and exact prerequisites. The selected Int Add FieldTail is discharged, but the top-level `1 + 2` result row remains unshaped and the `say` Display receiver remains deferred.

R327 also fixed a Types sample regression in selected-member HIR imports. Implicit prelude role-ID retention now scopes lookup to selected source roots, avoiding an unrelated recovered `text` export in `std::io::file`. All 45 playground library tests pass.

## R328 question

Determine why the selected `int.add` member's result type does not shape the result row of the imported `+` operator scheme, even though pinned source gives `int.add` the type `int -> int -> int`. Trace the exact graph rows, polarity, constraints, and source-owner lineage from the implementation member's imported call through the operator FreshUse and into `say`'s Apply argument. Establish a constructive source-to-candidate correspondence or a minimal counterexample before changing propagation. Do not inject an equality merely because both source shapes look like Int.

## Gates

The unchanged Console CLI must eventually produce `hello from Yulang\n3\n`; this remains unmet. Preserve the contravariant `[io]` meaning `[io,'e]`, which admits `[state]`. Keep unsupported, ambiguous, or unstable selection fail-closed. R149, source/native adequacy, every remaining sample, theorem closure, and production remain open.

## Verification at entry

- Focused Console Add/Display boundary test passes.
- `cargo check -q -p yu-playground` passes with existing warnings.
- `cargo test -q -p yu-playground --lib`: 45 passed, 0 failed.
- Exact unchanged Console `--run-module` CLI still returns `DeferredSelectionUnavailable`.

## R328 revision 3 evidence

### Add result through the actual Console Apply

The exact source trace now establishes that the selected `int.add` member's result row is the same live row used as the argument row of the Console `say` Apply. Before exact Add selection the row has no positive shape; after the source-backed Int member result relation is admitted, both the operator result and that Apply argument read back as `Int`. This proves the immediate Add-result-to-Apply-argument transport without adding a new equality.

The nested `Display.show` obligation is separate. Its receiver rows have no positive concrete bound; the examined row 89 has upper row 90 and row 90 has upper row 89. This trace does not yet provide the exact source-owner/FreshUse map from the imported `std::io::console::say` definition's generic argument to the nested `value.show` receiver. The remaining work is to trace that imported definition, its `where 'a: Display` obligation, captured graph, and same-invocation Apply mapping. Do not identify the Show receiver with the Apply argument from matching an eventual shape.

A minimal local generic function, `my apply x = x.echo; apply 1`, successfully selects the `echo` receiver shape as `Int`. This demonstrates that general Apply-to-generic-FieldTail propagation and the local definition FreshUse path work in that case. It narrows the unresolved seam to the pinned imported `say` route and its role prerequisite, without closing the full source/native bridge.

### Retained map accounting

The minimal regression initially hit the checked module-route scratch assertion. `FreshUse::bytes` counted `source_field_tail_obligation_rows`, but `RetainedFreshUseMaps::bytes` omitted the same retained vector. Adding its capacity to the retained byte total fixed the imbalance. The new generic FieldTail regression passes after the fix.

### CLI integration and package evidence

The two CLI integration failures recorded in rev2 are repaired. Absolute source paths now normalize to the same stable workspace-relative identity used by relative inputs. The error assertion continues to require a candidate-type conflict, preserving the all-observations-withheld check. `cargo test -q -p yu-playground` passes all groups: 45 library tests, 23 CLI integration tests, and every remaining package integration group.

The full Console output gate remains open with `DeferredSelectionUnavailable`. Current R328 contract is revision 3. R328 cap is 2400 seconds with 1368 charged at the time of this receipt; no carryover.
