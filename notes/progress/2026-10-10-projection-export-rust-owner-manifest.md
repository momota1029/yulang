# Selected projection export to current Rust owner manifest

Date: 2026-10-10
Baseline: `ad530c389`
Branch: `research/simple-sub-intrusion`
Status: bounded static source-to-Rust correspondence; research only
Claim class: field/owner manifest for native `id`; no new theorem
Review: unreviewed; producer used two read-only maps, not certification
Implementation, semantic selection and F5 cutover: none

## Purpose and authority

This manifest joins the selected native projection construction to the nearest
current HIR/solver/types owners for `my id x=x`. The selected semantic meaning
is already fixed by [native projection definition](../design/2026-10-08-native-projection-public-export-definition.md)
and [PE construction](../theory/2026-10-08-projection-public-export-construction.md).
The code side is a bounded inspection of `crates/yu-hir/src/module.rs`,
`crates/yu-solver/src/lib.rs`, `crates/yu-solver/src/shadow_apply.rs`,
`crates/yu-solver/src/shadow_f5.rs` and `crates/yu-types/src/lib.rs`.
This does not select a new Rust architecture or authorize production changes.

The semantic constructor is not the missing item: PE §4.2 constructs a fresh
ordinary root `u_i`, gives its active equations, applies one whole-frame action
and lets aliases reuse that same root. The unresolved work is to obtain the
authentic source/export inputs and connect that constructor to production
owners without reconstructing missing fields from F5 rows.

## Export and active-root fields

| Selected field | Semantic producer and consumer | Nearest current Rust owner | Correspondence status |
|---|---|---|---|
| `display = ForallAt(sigma,a,Arrow(a,result))` and original constraints | Parameter owns the original `Desc`; Source Generalize selects the final root; extraction emits the display. | `HirParameterId` (`module.rs:271`) and `LambdaRecipe` (`lib.rs:697`) retain structural ownership/positions. | No retained source scope, typed Desc or complete original constraints at the finalized scheme. |
| Fixed boundary `Omega` | Source publication retains the binding/provider anchor, intrinsic permissions, IF0 role/entry, `nu,K,D`, and full fixed dependency closure. | `DefinitionRootId` (`module.rs:185`) brands structural artifact identity; `SolvedModule` (`lib.rs:7333`) retains HIR and schemes. | No selected provider/world/permission boundary or source publication anchor. |
| `ValueInletSchema(q,a;Delta)` | Parameter owns the complete whole-carrier/Force/result/response/raw/future interface and its original scopes/constraints. | `ClosedValueScheme` (`yu-types/src/lib.rs:630`) stores arena, quantifier count, recursive-bound range and predicate. | No inlet or complete original `Delta` telescope in the closed scheme. |
| Ordinary Function head | Lambda owns the fixed raw closure and `GenericValueInlet(q,IF0)`; PE decodes the selected ordinary head. | `admit_lambda_fact` (`lib.rs:10790`) emits a signed Function constraint using the parameter row for id's argument and result. | Structural endpoints only; no fixed raw provider, generic inlet or original entry evidence. |
| Result and dependency | Source formation supplies `result=a` and `EntryValue` for id; pick separately supplies its fixed public dependency. | `PositiveValueView` (`yu-types/src/lib.rs:585`) exposes signed Function endpoints. | No source-owned result dependency or EntryValue interpretation. |
| Admission and production | The selected PE root has independent admission constructors and exhaustive production grammar with Echo. | `ClosedValueScheme` exposes the solved structural predicate. | No independent admission/history or production grammar. |
| Certificate families and original slot map | Extraction expands actual owning records while retaining typed identities, dependent telescopes, Shared/ViewLogic/EventField/EventProof classifications and proof choices. | `SolvedModule` keeps routed-use provenance; `shadow_f5::ClosedSchemeRef` keeps exact HIR/scheme identity. | No ordinary CE schema, original proof slots, event keys or scoped certificate choices. |
| Fresh `u_i` and whole-frame image | PE §4.2 chooses the frame before challenges, transforms all incident fields together, keeps `Omega` fixed, and aliases reuse `u_i`. | `instantiate_and_route_closed_inner` (`lib.rs:14795`) allocates Q/R rows and one ordinal substitution; `fresh_value_at_level` (`:9788`) stores row bounds, level and freshness metadata. | F5 fresh rows are type-solver variables, not frame-indexed ordinary descriptor roots. No joint action or alias/root identity law is present in this path. |
| Actual Direct readout | The selected consumer reads complete submitted root records and checks Value, Computation or Function evidence at the actual roots. | `root_value_for` (`lib.rs:16100`) validates a HIR root and returns scalar `Int`/`Never`/`Unknown`; `shadow_apply::CandidateExport` (`:91`, `:368`) combines that query with a borrowed scheme. | No Direct proof consumer or complete public-root readout is wired here. |

The selected export's fixed dependency closure and finite certificate slots are
not recoverable from equal printed scheme endpoints. In particular, the
`z=0` and `z=1` pick captures can have the same current scalar scheme while
their fixed values and retained dependencies differ; an F5 scheme pointer or
Q/R substitution does not identify those operands.

## Ownership order and first unmatched production input

The selected source-side order is:

1. caller/source registration supplies an authentic component, binder tree,
   declaration scopes and anchor incidence;
2. Parameter and Lambda construct their selected typed records and complete
   original telescopes;
3. source Generalize selects the actual final root and retain/fix result;
4. publication extraction constructs the source-free `ProjectionExport`;
5. decode allocates one ordinary root and one whole frame; aliases reuse it;
6. Direct consumes complete local proofs at the active roots.

The current HIR/solver route establishes structural definition, parameter,
lexical-use and Lambda joins, then finalized F5 schemes and Q/R instantiation.
It does not carry caller JointWF, original registration, source telescope,
publication, typed export, ordinary frame or Direct proof data. The earliest
unmatched item is therefore the concrete source-owner/application input, before
export extraction. Later rows in the table are separate missing correspondences;
the existence of a selected semantic rule does not fill them in Rust.

Do not adapt an F5 Q/R row as `u_i`, invent an empty `Delta`, infer an anchor
from empty captures, or publish a partial record. Any future production packet
needs the actual owner inputs and the selected resource/failure/lifecycle
decisions, plus its required implementation approval and review.

## Checks and limits

Method: exact selected-source inventory paired with bounded Rust symbol/body
inspection. No tests, builds, benchmarks, probes, code changes or question
directory reads. No repository-wide nonexistence claim is made. The current
Rust map is limited to the inspected HIR/solver/types path; equivalent owners
under other names or outside these paths were not adjudicated. Aggregate proof
statuses and F5 cutover remain open.
