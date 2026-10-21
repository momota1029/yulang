# R280 — evidence for qualified constructor Pattern application

Status: checkpointed parser evidence; provisional, unreviewed, no proof closure.

## Exact failure

Baseline `d6c2c4914` has 32 diagnostics on the unchanged pinned `lib/std/core/fmt.yu`: 15 `Missing/CaseArm`, 15 `ErrorGroup/OperatorChain`, one `ErrorGroup/Root`, and one `Missing/StringEscape`. The paired case diagnostics are anchored at arrows after qualified constructor paths with a same-line payload Pattern. A two-arm minimal CLI reproduction with `opt::just fill -> fill` and a long `std::data::list::list_view::leaf item -> item` reproduces the same pair. Existing tests establish GML continuation boundaries, and plain `f x` already constructs a Pattern application. The evidence therefore isolates qualified-constructor receiver state rather than claiming a general same-line application gap.

## Parent application and missing premise

R149 requires unchanged source and later authentic source-to-HIR correspondence. Supporting the constructor-plus-payload Pattern is a necessary parse step. It supplies neither semantic constructor identity nor a proof that binders are visited by every downstream consumer. R280 must retain the caller's arrow frontier and leave bare identifier behavior stable.

## Verification target

Observed parser-only result: all 30 paired diagnostics are gone, leaving exactly two diagnostics: ErrorGroup/Root at byte range 5801..5813 and Missing/StringEscape at 5800..5800, both on line 202. The source bytes and Git blob remain pinned. Focused Pattern and Case tests, exact diagnostic partition, playground check and static consistency checks pass. This says nothing about Pattern HIR traversal, role choice, sample output or source/native theorem closure.
