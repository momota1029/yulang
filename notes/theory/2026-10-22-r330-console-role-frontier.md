# R330 — Console role frontier and member projection

## Initial source trace

In the focused unchanged Console readback, the `value.show` receiver and `where 'a: Display` subject are distinct value rows. At the completed source schedule, both rows have the same four exact `IntPositive` lower atoms. Each row has a single direct upper edge to the other, with no exact upper atoms. The imported route maps the subject to the `Display` obligation and the receiver to the FieldTail in one FreshUse. The frontier counter starts at the receiver, follows positive lower rows, and counts only the receiver's upper edge; it does not traverse the reciprocal edge, so the old gate reports one negative row edge.

This is evidence for a narrowly source-qualified pair, not a general row equality rule. A provisional helper now requires one reciprocal live edge, equal current positive shapes, no other direct upper rows or exact upper atoms, exactly one same-FreshUse source field, and exactly one matching authenticated where-role subject. It leaves both row identities distinct.

## First falsifier

The focused Console test no longer reaches the old deferred-selection assertion. It fails while collecting the selected member projection with `Collection(MissingDefinitionEndpoint)`. This exposes a source/HIR collection seam that must be repaired before Console output can validate the selection hypothesis. The observation is not evidence that the output runs or that the selector gate is sound.

## Current code state

The source-qualified gate is experimental and must remain subject to falsification. The exact source member projection now tolerates separate authenticated HIR projections of one module while still rejecting a repeated identical artifact as `DuplicateModule`. Member selections retain both the provider FieldTail owner and, when uniquely matched by the same source obligation and receiver row, the outer operator use owner/occurrence.

Runtime lowering keys shared operator providers by their active use site. When a selected FieldTail belongs to a shared provider template, runtime may use its source-owned template selection only when every matching no-use template selects the same exact member root; disagreement remains unavailable. Member bodies are compiled once independent of the caller's operator-use occurrence. Host `write` lookup accepts either source import spelling (`out::write` or `std::io::out::write`) while checking the resolved export identity and signature.

The unchanged Console sample now completes ordinary inference and module execution with exactly `hello from Yulang\n3\n`. The Types sample's existing host-write execution and one-shot continuation tests also pass. Full `cargo test -p yu-playground` passed (all 45 library tests and package integration groups). Temporary `R330_*` traces and the temporary module inventory print were removed. These are implementation receipts, not proof closure.

## Open proof

Show that the complete ordinary source schedule and typed drain finish before field-tail selection. Show that selected method admission adds only receiver-negative constraints and cannot change the positive receiver/subject shape; account for nested member obligations and other pending tails that can share either row. If any later consumer can add positive shape evidence before selection stability is established, keep deferring and extend the pending-work fixed point instead of selecting early. The current focused and package tests do not establish this stability lemma.

The complete Yulang2 sample set, R149, source/native adequacy, original A/B theorem closure, independent review, and production remain open. Contravariant `[io]` still means `[io,'e]`, so `[state]` remains admissible and performed state remains in the residual.
