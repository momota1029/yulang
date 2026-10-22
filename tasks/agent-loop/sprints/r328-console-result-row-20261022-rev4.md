# Sprint R328 — Console result row and package regressions

Revision 4 records the cap boundary and supersedes revision 3. The sprint ends open; R329 continues the remaining exact port trace. Earlier revisions remain immutable history.

## Parent and scope

The parent objective remains all unchanged Yulang2 playground samples working through ordinary inference and execution, with source/native proof. R149, source/native adequacy, theorem closure and production remain open. Preserve the contravariant `[io]` interpretation as `[io,'e]`, which admits `[state]` and keeps state in the residual when performed.

## Result

- The selected Int Add FieldTail projects the pinned `int.add` source member with complete, stable evidence. Its result and the unchanged Console `say` Apply argument are the same live row and both read back as Int.
- The imported `std::io::console.say` FreshUse carries `where 'a: Display` and nested `value.show` together. The exact `std::core::fmt::Display` identity matches; reciprocal negative-side bounds connect the role subject and receiver, and both same-FreshUse gate checks pass.
- The nested receiver still has no positive concrete shape after the Apply argument becomes Int. The remaining source/native question is the Apply-demand/function-port transport from that argument to this imported FreshUse receiver.
- An attempted return-annotation endpoint change did not resolve the deferral and was reverted. No speculative equality or lasting annotation edit was made.
- Focused Console boundary test passes with its fail-closed expectation. The unchanged CLI still returns `DeferredSelectionUnavailable`.

## Open gates

Console output `hello from Yulang\n3\n`, R149, source/native adequacy, all remaining samples, A/B parent obligations, theorem closure, independent review and production remain open. No carryover from this 2400-second sprint.

## Handoff

Continue with R329: trace each exact Apply-demand/function port and captured scheme row through the same imported `say` FreshUse to the `value.show` receiver. Preserve owner, occurrence, graph root, row polarity and function port. Establish a constructive source-to-candidate correspondence before changing propagation. The durable R328 observations are in `notes/theory/2026-10-22-r328-console-result-row.md`.

Solo primary; no subagents. The active solver and playground paths remain held by the primary.
