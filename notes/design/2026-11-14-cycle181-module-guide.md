# Cycle 181 module guide

Status: Draft proof-engineering guide, 2026-11-14. Target: I-30's general
centered-ground EvidenceNode. No new general V5 field is closed.

| Modules | Main declarations and quantified result |
|---|---|
| GeneralNominalSemanticCompatibility181 | `compatible_extension`, `compatible_iff`: any finite family of arbitrary nominal origins, any existing centered model, and linked endpoint/origin names; semantic center coherence and old overlap are sufficient/necessary under the stated representative observations. |
| GeneralNominalObservationExtension181 | `extension_iff`: any finite family and any existing model; existence of old-footprint-preserving extension iff origins are inhabited, all observations fit, equal centers have equivalent observations, and old-overlap values agree semantically. No chosen representative premise. |
| GeneralDictionaryCenteredOverlapExact181 | `joint_model`, `compatible_of_joint`, `joint_iff`: any LinearLeafShape plan, matching journal context/bounds, PointNames and fixed journal model; complete plan extension iff nonpoint overlap observations agree with the old binder. |
| GeneralNominalBinderIdentity181 | `binder_fresh`, `binder_collision_iff`: same-seed nonoutput/nonpoint binders collide exactly at equal invocation/declaration/name. `registered_readback`, `registered_identity_readback` consume registered actual-use witnesses. |
| GeneralDictionaryCenteredProvenance181 | `compatible`, `joint`: any current Candidate with a linear leaf, PointNames, centered path, and syntactic registered-use Covered certificate. `installable`, `stable_instance` additionally retain separate raw Installable and value-support premises. |
| GeneralNominalSemanticCollisionExample181 | `semantic_extension`, `exact_assignment_impossible`: a concrete two-argument same-center family admits equivalent but unequal top/union(top,top) representatives; exact simultaneous values cannot be assigned. Not an inspected Candidate fixture. |
| GeneralNominalOriginAlias181 | `nominal_congr`, `structural_congr`, `mapSource_similar`, `observes_mapSource`, `observes_mapSource_iff`, `registered_alias_readback`: equivalent source renaming transports any nominal/structural path, without structural observation uniqueness. |
| GeneralNominalOriginRootAlias181 | `root_similar`, `root_observes_iff`, `certificate_equivalent`, `recorded_root_similar`, `recorded_observes_iff`: only the origin's one source root must agree; equality or two opposite current ordinary atoms supplies that agreement in every source model. |
| GeneralDictionaryCenteredAliasProvenance181 | `compatible`, `joint`: syntactic alias-covered registered uses produce overlap readback and a joint linear-plan model. Coverage itself remains a premise. |
| GeneralNominalOriginAliasExample181 | `recorded`, `observations`, `concrete_old`, `concrete_new`, `different_syntax`: concrete modeled ordinary equations transport actual nominal observations between distinct source-root syntax. |
| GeneralNominalLedgerReadback181 | `registered_actual`, `registered_readback`, `registered_alias_readback`: any modeled centered ledger already contains registered actual head-use equations; no path or raw packet registration is needed. |
| GeneralDictionaryCenteredLedger181 | `registered_covered`, `compatible`, `joint`, `alias_compatible`, `alias_joint`: consumes the preceding ledger equations without a path. Actual Candidate, LinearLeafShape, PointNames and plain/alias coverage remain explicit. |
| GeneralDictionaryCenteredLedgerExample181 | `candidate`, `modeled`, `binder_member`, `not_fresh`, `covered`, `nonempty_joint`: nonempty ledger with a real inspected Candidate and nonpoint old-binder overlap. FreshInputs fails, but joint model extension exists. Not asserted reachable/stable/novel. |
| GeneralNominalModeFrame181 | `schema_iff`, `variableSources_subset`, `schemaSources_subset`, `nonactual_singleton_iff`: all assignments agreeing on mode-sensitive schema support have equivalent SchemaHolds; endpoint uses need no additional binder agreement. |
| GeneralNominalModeLedger181 | `equations_iff`, `ledger_frame`, `centered_models_frame`, `centered_models_iff`: mode-sensitive schema support lifts through all plan equations/children/sites and the unchanged raw journal to full centered Models. |
| GeneralNominalFramedExtension181 | `compatible_extension`, `extension_iff`: finite extension over an arbitrary finite support list, with an explicit proved-frame parameter. The observation criterion is necessary/sufficient for support-preserving extension. |
| GeneralNominalModeExtension181 | `extension_iff`: instantiates the preceding construction with the proved mode-sensitive full frame; callers do not assume a frame theorem. Origins/endpoints must lie in this support, and the same four observation conditions remain. |
| GeneralNominalModeFrameExample181 | A concrete upper-mode singleton removes an unused binder from schema support; the old larger schema frame unnecessarily required that binder. This does not free a binder used elsewhere in a complete plan or ledger. |

Definitions, private helpers and generated declarations are included in the
new axiom gates, not just the public names above. `declarations.tsv` lists source
names. Full theorem types, including all quantifiers and model/shape premises,
remain in the referenced modules. There is no exported term of the unrestricted
G EvidenceNode in this cycle.
