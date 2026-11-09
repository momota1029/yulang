# Cycle 49: independent source semantics for the finite string adapter

Status: Draft. Date: 2026-11-09. Scope: finite string/equality source adapter only.

## Goal and boundary
Connect the computed finite adapter to an independent source-model relation, rather than defining semantic forcing using the adapter's own output atoms. The general diagnostic tree currently decodes slot endpoints as int or unknown (`CommonRoleMaterializedDomain.Endpoint.eval`), so connecting string success to that tree would require a separate carrier extension. Do not change that endpoint semantics in this cycle.

## Data and declarative relation
For every finite source occurrence table, seed slots, equality links, and named Index requests, a `SourceModel` is an assignment satisfying four clauses: each seed is string; equalities equate linked slots; equal source names equate occurrence slots; for every named request and every pair of matching occurrence slots, a string receiver implies a string output. This relation does not mention saturation, Derived, detection, output atoms, or the producer. It is the positive string consequence fragment, not all Index payloads or full language source semantics. Missing source names remain outside the compiled fragment; no source-parser coverage is claimed.

## Executable implementation and theorem types
Reuse the existing saturation and checked Index producer unchanged. For all tables/seeds/links/requests and all slots i:
- every `SourceModel` makes every independently `Derived` slot string;
- the separating assignment (string on derived slots, int elsewhere) is a `SourceModel`;
- `(forall a, SourceModel a -> Equivalent (a i).type str) iff Derived i`;
- for every output slot j, checked production at the saturation output succeeds iff all source models force receiver i to string;
- checked production is pending iff there are two source models disagreeing at i.

A successful named request contributes no new semantic restriction after saturation: its receiver being derived closes the request output too, so the producer's added output equation preserves every saturated ordinary model. This is an actual semantic fixed-point property, not merely an unchanged list of reachable slots.

Source models imply output-atom models. The converse is deliberately not claimed: output atoms forget the conditional constraints of unresolved requests. Thus equal string consequences must not be reported as equality of the full model sets.

## Evidence and remaining B4 work
Read audit `x-oracle.md` X13-X17 and spec 6.3. The old-runtime examples do not validate this source carrier; no new runtime check is claimed. No new language decision is made. General B4 still has five open bridges. This work strengthens source/closure/readout for one finite fragment only.

## Proved boundary
`output_models_not_source_models` supplies a two-occurrence witness with no seeds and one unresolved request. The ordinary output permits a string receiver and integer output, whereas the independent conditional source clause does not. This witness guards the exact scope of the general consequence-equivalence theorem; it is not the cycle's standalone deliverable.
