# R57 Rust owner projection handoff

Session: `EFFECT-PERMISSION-PROVIDER-NATIVE-CONTEXT/20261031-R57`
Admission: `tasks/agent-loop/history/effect-permission-provider-native-context-20261031-r57-admission.md`
Requested lane: Luna/high. Observed model/effort: UNKNOWN.
Rust work began after the primary RUNNING receipt; this handoff and the source projection are now frozen by hashes below.

## Owner-derived contribution

`ReceivingResidualExperiment::provider_native_context_projection` returns a private borrowed `ProviderNativeContextProjection` or an explicit `CurrentEmissionGap`. It composes the existing R55 `SourceInternalProjection` and R48 `ProviderEntryCertificate` from one `ReceivingResidualExperiment`, then checks that their Internal incidence, owner, admission, emission, provider view, facts, and path steps resolve into the same retained owner inventories.

The projection captures the complete effect-algebra view vector before exposing the selected provider view index. The existing provider search reads every view and every allowed member under `SCOPED_WORK_LIMIT`; zero, multiple, allocation-failed, or over-limit searches remain unavailable. The selected operation view must be the exact retained view, have a closed tail, and retain the exact provider occurrence and `Arc` declaration. Ordered support members and physical edges in both certified paths must point to their exact view/admission/emission/relation entries. No equal-family or endpoint-only fallback is used.

Retaining the two certified path vectors uses `try_reserve_exact`; allocation failure maps to `SearchLimit` instead of relying on infallible `Vec::clone`.

The R47 native owner projection now also retains and round-trip checks complete `InferenceSession.bounds` (`VariableBounds`) and effect-row inventories, in addition to complete state relation, dependency, origin/drain/completion, admission, and emission inventories. It records the session's canonical representative for every value/effect row separately from each raw row key. The existing raw source lower/upper and canonical source lower/upper endpoints remain separate. `VariableBounds` retains its exact integer/unit lower flags as well as row and atom vectors; effect rows retain their bottom/empty flags. Converters must preserve those fields when constructing R47 `RowBounds`.

R55 retains complete batch `ConstraintOccurrence` facts and complete store `SemanticFact` facts in separate indexed vectors. `ProviderFactOwner::BatchOccurrence` tags the Catch fact index, so an equal integer in the semantic-store namespace cannot select it. Internal semantic facts are checked against the exact unique entries in the separate semantic inventory. The source/Internal projection continues to retain the same batch's HIR Arc, source roots and local sources, full formal/call/recipe/schedule/owner/component inventories, entry permissions, lambda origins, routed uses, and exact Internal root/function witnesses. It keeps parameter-native-root provenance distinct from the recipe/root-component-derived registered root.

The projection is an owner-evidence bridge for R47/R48/R49/R55 construction. It does not itself instantiate the Lean R50 `Context`, establish the Rust-to-Lean interpretation, or close any parent theorem. Those remain proof-lane/source-correspondence obligations. This private projection changes no forwarding or inference behavior and has no authorization consumer.

`certified_lower_paths` does not return a traversal trace. The source correspondence must connect its bounded exhaustive walk, including its second-path rejection, to the singleton path candidate tables; no persistent trace is claimed here.

## Source review and checks

Reviewed the exact existing `provider_entry_certificate`, `current_internal_emission`, `certified_lower_paths`, `OwnedResidualProjection`, and `SourceInternalProjection` owner paths. The R57 selection remains based on their existing identity- and occurrence-qualified reads. Candidate-search failure, ambiguity, and work-limit exhaustion remain unavailable.

No build, test, Cargo, Lake, or type-check was run, as required by the Rust lane. Permitted source-integrity checks and final hashes are reported after this handoff is frozen.

## Exact files

- Changed source: `crates/yu-solver/src/candidate_receiver.rs`
- `crates/yu-solver/src/candidate_context.rs` is unchanged.
- This handoff: `tasks/agent-loop/inbox/effect-permission-provider-native-context-r57-rust.md`
- No other path was written by this lane.

## Frozen inputs and outputs

R57 revision-2 contract: `8f4d18e5954588ebd9cf9524e5bf5af56abc688aaac333d183de9a9e94a24576`
R57 admission: `7c57f2fcca09a9fd21c88ee20396ff813072fe9363516787675f5ecdd035a7c9`
R47 Lean: `d64c54f7c977e110305a76e6437fc87c8ff14201a4d69eb0bbcb5ee0e1cd8b9c`
R48 Lean: `b85dfad5c0e80f7fbc2480e7f38421cc6c50107144d9abb160e688208b192575`
R49 Lean: `4fc4380f3ad1827ecf155f982e5186b32d6d66d91909039fb118063d8f1e2df2`
R55 Lean: `7aaecdd3d358d769123f00acb4b19b4d7d61ccfef98fee4eb53179da4a105123`
R56 review: `798af26df1b878a9b67cb6996b5ef3aea00c9e60915d8780e81d0f753f8ba165`
R55 Rust handoff: `db9e9a2fcd545502f501e103d40a66fa41343c7906e44efca4e1d72087f48b4f`

Final source and handoff hashes are supplied in the completion receipt to Luna. A fresh independent review is still required; this handoff is not self-certification.

## Revision 2 — R47 row interpretation correction

This correction supersedes the sentence above saying that converters must preserve `VariableBounds` and effect-row flags when constructing R47 `RowBounds`. The Rust projection retains the native `VariableBounds` integer/unit flags and `EffectBounds` bottom/empty flags as part of the borrowed source records. R47 `RowBounds`, however, contains only four physical vectors: lower rows, upper rows, lower atoms, and upper atoms. This Rust change provides no flag reader, does not map those flags to additional vectors, and establishes no universal flag-to-vector invariant. The R47 interpretation must use only the four physical vectors unless a separately authorized source correspondence establishes more.
