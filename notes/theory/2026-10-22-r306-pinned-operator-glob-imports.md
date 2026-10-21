# R306 — pinned operator glob import boundary

Status: READY, exact syntax import route repair; parent R149 remains OPEN.
Baseline: commit `aedb4d6e6`.

## Entry evidence

The R305 positive controls show that when a `HirOperator` exists, the selected table site and imported dependency receipt can be retained without changing operator semantics. The exact pinned `lib/std/core/fmt.yu` source gives a counterexample earlier in the pipeline: its four leading `use` declarations include three module glob imports, but `HeaderInfo` retains only the explicit `std::num::frac::frac` route. Consequently the selected syntax environment lacks `lib/std/core/ops.yu`, and the `+` in `Display.say` is a token directly under the root CST, with no HIR operator at that range.

## Governing design and proof constraints reread

The converted unified design §§4.1–4.5 requires source occurrence identity and semantic payload to travel together while remaining distinct from transformed endpoints. Stages 3 and 4 preserve ordered tuple structure and delay method selection until relevant bounds settle. The proof companion §§4.1–4.5 warns that local capture evidence is not the full boundary/dependency/observation theorem. The effect correction remains: contravariant `[io]` denotes `[io,'e]`, so `[state]` alone is not a violation.

R306 follows the exact `use` source nodes through header projection and pinned dependency selection into the already-established operator-site provenance API. It does not resolve the operator value, introduce `.add` rewriting, form a member scheme, or close any original theorem. The source/native, A/B, principal-type, termination and production gates remain OPEN.

## Falsifiable outcome

The same pinned fmt bytes must retain the three glob routes without making `*` a path segment, select the pinned `core/ops` source with its exact content revision, and associate the original `Display.say` plus token into HIR with the exact imported Infix site. Named imports, separators, unresolved routes and recovery must remain discriminating controls. Only after this connection exists can a separate boundary trace the operator declaration's original value owner and continue toward the deferred member candidate path.
