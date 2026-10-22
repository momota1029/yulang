# Sprint R326 — run unchanged Console through the whole-module source schedule

Revision 9 supersedes revision 8 only for the source-import result and current solver action. Revisions 1–8 remain historical contracts.

Status: ACTIVE, solo serial lane. Baseline remains `3a9aea751` plus the uncommitted R326 runtime and source-projection work. R149 and the parent goal stay open.
Authority: unchanged user goal and `notes/design/2026-10-20-r149-types-console.md`. Preserve original bytes, source identities, role/impl semantics, and the correction that contravariant `[io]` means open `[io,'e]`, so `[state]` is permitted.

## Current bounded result

Selected source imports now ignore local declaration names when resolving the implicit prelude. This lets the authentic `std::text::str` projection pass a recovered unrelated prelude export. A two-segment operation path such as `out::write` now resolves through either the exact imported family export or the same file's exact Act declaration. The focused selected-Console test checks family and operation identities.

The unchanged 92-byte Console source passes source projection and operation preflight, then returns `Solve(DeferredSelectionUnavailable)`. Runtime output is not achieved. The `say` FieldTail receiver has an upper-bound relation to its authenticated `Display` role subject, but the concrete top-level integer argument has not supplied a positive shape to that FreshUse receiver. `println`'s string `Add` receiver is selected. Nested operator FieldTail obligations are retained with their enclosing definition graph and replayed through its FreshUse. One requested `int: Add` member source remains unavailable in the projected world.

## Next work

Trace the source `Apply` for `say: 1 + 2` from its exact argument endpoint through the instantiated function input and into the `show` FieldTail receiver. Determine the required row directions from the captured function graph and FreshUse maps; do not synthesize equality, close effect rows, or infer shape from an unrelated upper frontier. Add a focused invariant test for the transport, then re-run the exact CLI and preserve fail-closed behavior for missing or unstable selection. Continue through the selected `int: Add` source projection, host writes, and the entire unchanged Yulang2 playground sample set. No theorem closure, source/native adequacy, R149 closure, or production claim follows from these executable results.

## Constraints

- Exact source bytes and expected output remain unchanged: `hello from Yulang\n3\n`.
- No subagents or background work. No blanket staging, history rewrite, or forced push.
- Keep the existing leases from revisions 1–8: HIR module source resolution, solver candidate source/effect/scheme/shadow apply, playground runtime/projection, R326 note and current state.
- The R326 cap remains 2400 seconds with no carryover. Update the active charge honestly and stop this sprint at its boundary; continue the parent goal in a new bounded sprint if necessary.

## Verification status

`cargo check -p yu-playground` passes with existing warnings. Focused tests for exact Console operation identity and the Console selection boundary pass. The exact CLI does not yet produce output; it fails at `DeferredSelectionUnavailable`. Whole-playground tests, source/native proof, independent review, R149 closure, all-samples completion, and production remain open.
