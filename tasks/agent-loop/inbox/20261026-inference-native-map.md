# Native inference map and first soundness packets

Date: 2026-10-26. Assigned baseline: `0f6346a2de0a8bff863f41d487eb4b29cf8fb5f3`, yulang3. Read-only mapper: `/root/inference_frontier`. No checker/test/compiler/Git/cache/child activity. This receipt is the sole write.

## Material finding: native SCC qualification still implements the old rule

`crates/yu-solver/src/candidate_value_graph.rs` stores semantic `Value` identities, adjacency/reverse adjacency, extrusion event associations and one `components` vector. It stores no Value birth. `Graph::seal` (315) runs iterative two-pass SCC on the entire compressed graph. `Graph::qualifies` (340) compares the components of the event's origin and receiver without any birth restriction.

The authoritative `notes/design/2026-10-24-birth-level-scc-intrusion.md` requires SCC in each induced semantic graph G_k, all path vertices at birth k. It explicitly states that its approval did not include an implementation change. Current Rust therefore cannot be certified as implementing this current rule.

An existing source-grounded discriminator is already available: `my loop x = { my helper y = loop y; helper x }`. The source planner assigns loop birth 1 and helper birth 2. `candidate_intrusion_tests.rs::nested_definition_source_owns_real_call_demand_extrusion` (310) asserts both events qualify and their real parent/copy rows merge. `tests/candidate_intrusion_observation.rs::retained_nested_calls_observe_actual_value_scc_and_equated_pairs` (31) asserts the same through the public observer. The current rule makes these two cross-birth events nonqualifying. I inspected these tests; I did not run or change them. This proves a qualification-rule mismatch, not an accepted-ill-typed source counterexample. Expected-result changes require the primary's explicit correction handling.

A second exact graph discriminator is u→w→v→u with births u=v=1,w=2. Equal endpoint birth plus global SCC incorrectly qualifies (u,v), whereas G_1 does not. Self-occurrences remain qualifying even without a nontrivial cycle.

## Exact immutable birth owners and repair feasibility

The current source planner already determines the relevant generation levels independently of mutable solver rows. `candidate_source.rs::emit_candidate_source` starts `Work::Visit(body,1,definition_region)` at 1204. It stores immutable source-plan `component_levels` and `parameter_levels`; `initialize_candidate_source_levels` later copies these into mutable live levels. Row extrusion, quotient minimum levels and fresh-use levels must never be read back as birth.

| Semantic Value identity / allocation | Existing source birth owner |
|---|---|
| `Module(DefId)`; `Graph::register_module`40, root intern97; module mapping installed by `lib.rs`1075 | Its source root starts at level1. Registration may precede body collection, so retain declaration birth rather than first Name-use level. |
| `Local(HirLocalId)`; intern at graph201/212; Names at107/235 | `Work::Initializer`1516 receives the enclosing block level+1 from1345–1368. The whole initializer and its formal/body generation use that level. Later Names keep this identity/birth. |
| `Parameter(HirParameterId)`; resolved Names and expression receiver intern | Root parameters1 (1086). Lambda parameter and record-pattern binders use the lambda's current level (1274–1296); lambda bodies/defaults do not increment it. Retain birth at declaration, not first reference. |
| `CatchBinder` including case binders; graph115/134/139 | Catch/Case arm construction at1380–1470 uses the enclosing current level. The planner already deliberately preserves the arm-level representative when the first Name occurs inside a deeper initializer (1218). Even unused graph binders require declaration birth; lack of a solver row is not a reason to omit it. |
| `Expression(HirOccurrenceId)`; source/member root, If/StatementBlock/Sequence/Record/Tuple/Variant/Apply results at240–297, fallback callee values via `expression_value`80 | The owning `Work::Visit(index,level,region)` supplies its source level. Ordinary children, group/ascription, lambda bodies, branches and field/payload elements inherit level; only nested binding initializers increment. Group/ascription/Name receiver resolution must preserve the existing resolved semantic identity. |
| Fragment helper vertices at222–230 | Not semantic Values and outside birth's domain. Their source-expression level can be representation metadata only after proving helper projection for each G_k. |

All semantic vertices enter through `Graph::intern`45; helper vertices alone are pushed directly. `retain_source` is currently called at source1071, before the level walk. A faithful repair can build birth census alongside that actual walk and attach/defer it until all source owners are collected, or move graph construction after the census. The complete declared identities must be covered before seal. Duplicate identity birth must agree; missing birth cannot silently become zero or a use-site value. Root expression/member/provider and imported-module collection paths need explicit coverage.

All operational consumers of qualification are in `candidate_intrusion.rs`: `retain_extrusion_parent`305/325, `finish_candidate_extrusion`368/383, and `recapture_candidate_extrusion`388/393. Each asks whether any retained source event qualifies. `shadow_apply.rs`1272 reports the result; test consumers are additional. `settle_candidate_intrusion`568 drains retained pairs into `merge_candidate_rows`599, which preserves both physical bound sides, takes minimum live row levels, ORs non-generic flags, canonicalizes provenance, and replays bounds. Birth should remain outside that row mutation.

### Helper representation seam

The existing graph compresses Name incidence with shared fragment paths to keep construction linear. Ordinary helper links follow same-level direct children. StatementBlock helpers explicitly exclude binding initializers (255–260); those initializers become separate semantic owners. A promising efficient representation proof establishes (a) semantic-to-helper edges preserve the source birth/representation level, (b) helper-to-helper edges preserve that level, and (c) each helper-only path contracts to exactly the actual semantic incidence, with converse expansion. Then one SCC computation over justified same-level compressed edges can represent all G_k. This is a proof obligation, not already established here. Assigning arbitrary helper births, filtering only endpoints, or recomputing the full graph once per level without a cost justification is not an acceptable shortcut.

The authoritative rule and actual source walk supply the semantic choices for these constructors. Representation, forward-reference completeness, helper projection and cost remain implementation/proof work; no new inference rule is needed.

## Native inference pipeline and secondary proof target

| Stage | Actual owner and data |
|---|---|
| Generation | `candidate_source.rs::emit_candidate_source`, `Work::{Visit,Finish,Initializer,Install,CatchArms,CaseArms,...}`, immutable `Plan` schedules and source IDs. Literal Finish1559 emits both value bounds and bottom/empty effects. If1633 checks each condition Bool and retains every branch's constraints/effects; no branch execution. `shadow_apply.rs::CandidateRelation`3443 carries authentic Group/Apply/Record/Tuple/Variant and pattern recipes. |
| Source action execution | `candidate_source.rs::execute_candidate_action`2423 dispatches retained facts, candidate recipes, local installation and use, annotation, operation and formal actions. Planning itself admits no constraint. |
| Typed propagation | `lib.rs::constrain_live_item_with_inferred_entry`13991 routes candidate mode to resumable typed drain; `dispatch_live_item`14432 and `candidate_step_function_dispatch`14955 retain actual pending work/provenance. Function decomposition14800 emits four typed ports: upper.argument≤lower.argument, upper.argumentEffect≤lower.argumentEffect, lower.resultEffect≤upper.resultEffect, lower.result≤upper.result. |
| Bounds/replay | `candidate_extrusion.rs::candidate_insert_bound_with_evidence`702 appends the exact selected one-sided bound and retains physical-slot readback. `candidate_replay_bound`1070 creates each lower≤upper in the correct polarity order and records both source relations. `candidate_apply_value`1114 chooses owning row/side based on actual live levels. `VariableBounds`/`EffectBounds` at lib4190/4215 each have direct lower/upper rows and exact nonvariable lower/upper endpoints. |
| Extrusion | `candidate_extrusion.rs::candidate_extrude`24 uses operation-local `(endpoint,polarity,target)` keys, separate row/structural memos, memoizes a fresh row before selected-bound descent, retains actual parent/copy/occurrence, and adds the opposite-side source link. Value and effect kinds remain distinct. The separate legacy `lib.rs::extrude`13546 lowers reachable levels and is not this polar-copy algorithm. |
| Generalization/use | `candidate_scheme.rs::capture_candidate_graph*`2520–2557 retains typed nodes, both bound sides/evidence, regions and obligations. `Capture` row eligibility1761 is `level>boundary && !non_generic`. `freshen_candidate_graph`4140/4250 canonicalizes captured rows, uses one canonical-row map, freshens only still-eligible captured-local representatives and shares others. `install_candidate_local*`4732–4754 captures the source boundary; later `route_candidate_local` reconstructs through the retained scheme. |

Useful existing focused tests include nested/acyclic occurrence qualification and real polar pairs; `nested_apply_fragments_have_bounded_linear_storage`; source conditional direct-child occurrence retention; deferred-call constraint retention/late conflict; four typed function-port pairwise-swap rejection; and capture/fresh-use tuple/record/variant alias and polarity preservation. They are regression evidence, not soundness proofs.

## Small coherent construction packets

1. **First: induced semantic-graph qualification and helper projection.** Fresh suggested module `YulangClosure/NativeBirthQualification.lean`. Construct finite path contraction/expansion for the actual compressed shape with semantic vertices distinct from helpers; prove equality of induced reachability and therefore qualification, cross-birth edge irrelevance, reflexive self qualification, and the three-vertex shortcut falsifier. Tie birth assignment to the existing source walk and retained immutable IDs. A theorem whose premise already says compressed reachability is correct would miss the critical bridge. This directly enables correcting the stale native criterion.
2. **Then: native constraint discharge.** Fresh suggested module `YulangClosure/NativeConstraintDischarge.lean`. Formalize the actual kind-separated endpoint/bound store and four-port decomposition against the existing Simple-sub constraint interpretation. Prove the exact append/replay worklist invariant: satisfying the represented residual store and obligations implies the original generated demand; insertion preserves old demands, replay is the actual ordered lower-to-upper consequence, and all four Function children reconstruct the same parent comparison. Include actual polarity/kind cases and pending/memo completion, not an assumed dispatcher-soundness field. Apply it to a concrete retained source literal/conditional/Apply emission. This is native constraint soundness; complete source Call realization remains a separate theorem.
3. **Next: capture/fresh-use solution transport**, using the actual one-map canonical-row reconstruction, preservation of shared/non-generic anchors and all bound/evidence fields. Prove it for the exact captured graph before composing intrusion/generalization. Do not replace the source's dependent telescope with an unscoped valuation and call it original A/B.

## Original claim boundaries

Even corrected induced-SCC qualification does not prove that adding every qualified equality preserves all source solutions. The current consumers use `source_events(...).any(qualifies)`. `2026-10-24-concrete-extrusion-source-realization.md` section5 explicitly leaves the retained occurrence's receiving-Value correspondence and arbitrary support-selection justification open. `2026-10-24-birth-level-scc-intrusion.md` BL-JOINT still requires telescope/full-domain evidence and publication/use compatibility; same birth is not same scope. `2026-10-24-source-indexed-constraint-derivation.md` retracts SC4's record-rebind realization and distinguishes generated obligations from their semantic realization. These cannot be supplied as soundness premises under a different name.

No actual accepted-ill-typed source counterexample was established in this map. Original whole-source/native A/B soundness, principality/coverage, naturalness and termination retain their complete domains and quantifiers.

## Source snapshot

The paths below were read in this packet; hashes identify the source snapshot for follow-up construction.

| Path | SHA-256 |
|---|---|
| `AGENTS.md` | `ce73e9754ba9fd00bd2c4395d322ce77730a26aafb586d51de8ad169d7f8d48f` |
| `AGENTS.pre-sprint.md` | `34b8b8169696dcc6a0899204226914d250ddecf6782d14be670b7b2d5352c562` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |
| `notes/design/2026-10-24-birth-level-scc-intrusion.md` | `ceedbb24ea2f9a640574840e840de7121c8f9b94a5c83ab50efc7a819badf5ae` |
| `crates/yu-solver/src/candidate_value_graph.rs` | `5893555fe89c594feabca200d1d8f26631877200da61e6ae39c80d375f748bb1` |
| `crates/yu-solver/src/candidate_source.rs` | `57b119592a6a8d4afd42aca10c5e2bb749cfdf0fb0fdea967dd437d552a1a04e` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` |
| `crates/yu-solver/src/candidate_context.rs` | `33af2efb6ed782e4f143cccff03c62087e6ba8d0fbe90415846537fc2a08cec5` |
| `crates/yu-solver/src/candidate_scheme.rs` | `02349de1a2d69289eb348f7ff807a9e36faa2e2028cf61d10c1af9cd364409c5` |
| `crates/yu-solver/src/shadow_apply.rs` | `f8d92f2d59353e5b9cda014545b352c8d6356cc0aff3b4eeae0e81893e78202d` |
| `crates/yu-solver/src/lib.rs` | `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` |
| `crates/yu-solver/src/candidate_intrusion_tests.rs` | `30cbf8b9a3ab11e9448d2ea5aa47ee40aa3d80d0ee2bceec1e1b1abb6b1393d3` |
| `crates/yu-solver/tests/candidate_intrusion_observation.rs` | `04a876b9fe0a3a45f2d1996446a11d0b36dce3bb26ad02537118e4853e4b78e1` |

Writes stopped at 2026-10-26 01:04:12 UTC. Sole write: this handoff. No running processes or descendants.
