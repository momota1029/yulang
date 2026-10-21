# R278 — Yulang2 dotted Pattern target

Status: checkpointed, provisional primary construction, unreviewed. R149 sample
inference, standard-library role selection, output, source/native proof and
production remain OPEN.

## Parent application

R277 pinned and classified the parser failure for the exact `fmt.yu` source.
The R149 role and implementation declarations use ordinary Binding targets
`a.show` and `value.show`. Historical Y2 source and parser evidence identifies
these as `IdentifierPattern` plus dotted `Field` continuation. The Y3 Chasa
design intentionally deferred DotField in Pattern while preserving it for a
separate addendum. R149's adopted unchanged-source requirement directly
selects these forms as required syntax.

R278 adds only the parser representation: `PatternFieldTail(Dot, Identifier)`
under Pattern, with adjacency and recovery ownership. This should remove the
target-related portion of R277's root recovery groups. No method semantics,
role registration, imports or HIR admission follows from the CST.

## Verification

The focused role/impl fixture parses without structural diagnostics and retains
the exact `PatternFieldTail(Dot, Identifier)` nodes. Focused tests cover chained
members, missing members, the binding-colon recovery frontier, a spaced dot,
`..`, and a non-identifier receiver. The exact pinned `fmt.yu` census now has 36
diagnostics. The corrected four-category R278 census is 21 root `ErrorGroup`s,
7 `OperatorChain` `ErrorGroup`s, 7 missing `CaseArm`s and 1 missing
`StringEscape`, down from R277's 50. The earlier subtotal omitted the
`StringEscape` category. Its exact source identity and bytes remain pinned.
`cargo check -p yu-playground` passes. The sprint static and diff checks are
recorded in the handoff after close.

This removes parser recovery at the two dotted target forms only. The remaining
root recovery, expression errors, HIR admission, role resolution, sample output,
source/native theorem and production gates remain OPEN. The source bytes and
expected sample outputs stay unchanged.
