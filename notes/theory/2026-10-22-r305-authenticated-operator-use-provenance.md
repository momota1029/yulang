# R305 — authenticated operator-use provenance

Status: OPEN_CONTINUATION, provenance receipt API implemented for associated operator uses; pinned Types source connection is blocked; parent R149 remains OPEN.
Baseline: commit `3ece25edf1ab84fd543c4e311b890a70f97c60d5`.

## Governing material reread

Reread the converted unified design §§4.1–4.5, stages 3–6 and §§9–10, plus the proof companion §§4.1–4.5 and §2.12.1. The design requires source identity to remain distinct from transformed endpoints and semantic payload. Its method stage delays selection until relevant bounds settle. The Capture replacement theorem applies only after its boundary, dependency closure and observation conditions are established. No local provenance test closes those obligations.

The proof companion's callback example also restates the user's correction: contravariant `[io]` means `[io,'e]`; passing `[state]` by itself is therefore not an effect violation. Permission remains separate from the actual callback effect.

## Source evidence

The unchanged Types source retains `pub a.say = std::io::out::write: a.show + "\\n"` in the pinned `Display` role. The pinned `std/core/ops.yu` header declares public `+` with its own value body. The ordinary parser can associate imported operators when its selected syntax environment contains that dependency. The pinned `std/core/fmt.yu` parse did not receive the dependency because header discovery omitted its glob imports.

`HirOperator` currently stores only spelling, fixity and the consumer token range. The retained `OperatorTable` has one `OperatorDeclarationSite` per fixity, with `OperatorOrigin::{Local, Imported(SyntaxDependencySlot)}` and the declaration range. `SyntaxEnvironment` maps that slot to `SyntaxDependencyProvenance(module_label, revision)`. `ParsedFile` retains both the selected syntax environment and exact effective operator table. The data needed for an occurrence-to-declaration-site provenance receipt therefore exists across the syntax parse, but HIR drops the chosen site when it constructs `HirOperator`.

An additive read-only `OperatorUseProvenance` receipt now joins the existing site, slot and dependency records without changing parsing or operator meaning. `HirOperator` retains it, while its own source range stays separate from the provider declaration range. Focused local and imported positive controls pass, including exact dependency label/revision and declaration range.

The original pinned `Display.say` occurrence remains outside HIR. In the parsed fmt module, `HeaderInfo` exposes only `std::num::frac::frac`; the three glob imports at the file head are absent, including `std::core::ops::*`. The selected syntax environment has only the frac dependency. The exact `+` token is retained directly under the root CST, not under an expression node, and no `HirOperator` is associated at its source range. Thus the parsed operator table has no `+` Infix site and no source-use receipt can be claimed. This is a concrete counterexample to the original R305 end-to-end target, not evidence that lookup by spelling is sufficient.

## Narrow target and limits

For associated uses, R305 preserves the selected site and dependency receipt into HIR. The local/imported positive controls identify origin, fixity, dependency slot, exact module label/revision and declaration range. The original pinned `Display.say` source falsifies the full bridge because its glob dependency is lost before parsing. The next exact owner is header import projection and the pinned syntax-environment planner; these paths require a new lease.

The result does not yet connect the declaration range to an exported value owner, lower the operator into candidate constraints, or type the `Display.say` member. It does not prove selection, Capture preservation, evaluation, principality, runtime or source/native correspondence. No source rewrite to `.add` is sound in the general case.

## Parent application

The generic HIR receipt proves only that the parser-selected origin can be retained on already-associated operator uses. The original `Display.say` source still needs its glob import route before the operator occurrence can enter HIR. After that, the exact exported value/body owner remains a separate step. Member candidate formation, unchanged Types/Console execution and all source/native, A/B, principality, termination, review and production gates remain OPEN.
