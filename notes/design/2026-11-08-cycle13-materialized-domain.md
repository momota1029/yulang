# Cycle13: state-dependent finite request domain

I-7 bridge2 partial: extend fixed-endpoint potential closure with finite source templates.
Data: endpoint syntax with fixed Ty, source slot (Fin n), unary wrap. A slot
uses the existing ordinary materialize: actual int evidence maps to Ty.atom.int,
otherwise unknown (str deliberately not encoded as a nominal Ty).
A source request keeps its own lower/upper templates, so endpoints may differ.
Executable domain enumerates unknown/int choices at every slot, forms all root
requests, then takes the existing all-candidate checked-Paterson closure.
Independent judgment: some enumerated root reaches q by declaration Step.
Theorem: for every registry, finite list of source requests, arbitrary state,
source in that list, and actual filtered producer child of any reachable request,
that child belongs to the one state-independent computed domain. No external
closure premise and no fixed concrete declaration example.

Limits: int-only materialization adapter, not general interval bounds inference.
Repeated slot occurrences can be overapproximated independently in the finite
list; completeness of domain membership is not semantic feasibility. Dynamic
source-template creation, shared source provenance/allocator, and saturation are
still missing. This is not the general generated_work_closed bridge.
Yulang2 oracle X13-X16 is context; this internal domain enumeration has no runtime
counterpart and is not claimed runtime-validated. Existing materialize uses
ordinary evidence, never singleton impl guessing (spec6.3).
