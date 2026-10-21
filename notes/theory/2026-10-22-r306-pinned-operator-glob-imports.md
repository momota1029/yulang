# R306 — pinned operator glob import boundary

Status: local source-to-HIR provenance RESULT, unreviewed; parent R149 remains OPEN.
Baseline: commit `aedb4d6e6`.

## Entry evidence

The R305 positive controls show that when a `HirOperator` exists, the selected table site and imported dependency receipt can be retained without changing operator semantics. The exact pinned `lib/std/core/fmt.yu` source gives a counterexample earlier in the pipeline: its four leading `use` declarations include three module glob imports, but `HeaderInfo` retains only the explicit `std::num::frac::frac` route. Consequently the selected syntax environment lacks `lib/std/core/ops.yu`, and the `+` in `Display.say` is a token directly under the root CST, with no HIR operator at that range.

## Governing design and proof constraints reread

The converted unified design §§4.1–4.5 requires source occurrence identity and semantic payload to travel together while remaining distinct from transformed endpoints. Stages 3 and 4 preserve ordered tuple structure and delay method selection until relevant bounds settle. The proof companion §§4.1–4.5 warns that local capture evidence is not the full boundary/dependency/observation theorem. The effect correction remains: contravariant `[io]` denotes `[io,'e]`, so `[state]` alone is not a violation.

R306 follows the exact `use` source nodes through header projection and pinned dependency selection into the already-established operator-site provenance API. It does not resolve the operator value, introduce `.add` rewriting, form a member scheme, or close any original theorem. The source/native, A/B, principal-type, termination and production gates remain OPEN.

## Outcome

`HeaderImportSelection::{Path, Glob}` now records whether a route imports one name/path or a module glob. The header importer projects all three original fmt globs as module routes without adding `*` to route segments. Filtered globs remain fail-closed because `HeaderImport` does not yet carry exclusions. The pinned syntax environment for the original fmt source now includes core/ops, data/opt, num and num/frac with their exact revisions.

The original `Display.say` plus is an associated HIR operator. The regression verifies that its source range covers the exact `+` token, its selected `OperatorOrigin` is Imported(slot), that slot selects `lib/std/core/ops.yu` at the pinned revision, and the declaration range points into the original pinned `pub infix (+)` header. The operator use range and provider declaration range remain separate identities. Header glob and failed-projection controls, pinned fmt inventory, syntax/playground checks and the unchanged Types boundary test pass.

This only reconnects source import selection to HIR operator provenance. It does not resolve the operator declaration's exported value owner, lower it into a candidate constraint, type `Display.say`, select an implementation, or execute Types/Console. The next source owner is the original operator declaration value/body and its candidate consumer; all theorem and production gates stay OPEN.
