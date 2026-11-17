# Cycle237: selective aggregate completion beyond private HeadModels

Keep the I44 semantics and all earlier counterexamples unchanged. Investigate
actual head-schema preservation, exact capture Fits, and actual child equations
under the explicit selective aggregate patch from cycle236. First prove real
support/transport facts, then use them to identify the remaining simultaneous
materialization obligations. Do not assume fullHolds or assert independently
chosen witnesses coincide. ProtectedCovered/source provenance is another worker's
assignment. New files only, direct trust-zero compile and axiom audit.

Counterexample-first check: private HeadModels alone does not constrain actual
binders or output names, so it cannot imply fullHolds. Existing HeadSharing is
only pairwise observation compatibility, not yet equalities to a protected
actual binder. Any theorem must keep this distinction explicit. General source
reachable selected-to-complete materialization is the goal, not a premise.

## Verified results

Thirteen new modules, 62 public declarations, direct Lean `--trust=0
-DwarningAsError=true` and combined import/axiom audit PASS. Only propext,
Classical.choice and Quot.sound. No changes to old modules or kernel semantics.

1. SelectiveHead237 transports actual head schema and sharing under aggregate
   patching; SelectiveChild237 transports every actual child schema.
2. CurrentProjection237 derives centered inspection projections from current
   Frame, full journal Models, actual schema tests and sharing. No old-kernel
   reachability or extra point-input assumption is used.
3. ProjectionBounds237/CurrentHead237 derive all capture Fits from current
   private HeadModels and actual head schema in that same full journal model.
4. ModePattern237/ModeCompiler237 prove normalization for mode-sensitive pattern
   evaluation and exact compilation in every mode. Nominal applications force
   actual evaluation even within lower/upper mode. Thus normalized scope,
   including shadowed record fields, suffices; no raw lexical scope is added.
5. ModeIntervals237/ChildIntervals237/ChildClosure237 derive every child interval
   Fits from generated lower/upper equations and actual child equations. On an
   actual source-reachable state and current Frame, fullHolds in a full journal
   model is equivalent to private HeadModels + actual head schema + total
   Outputs + all actual child schemas. This is a reduction, not existence of
   a simultaneous model for these four components.
6. HeadReplay237: headSchema is independent of raw observation versions when
   declaration/constructor/interpretation and actual center lists agree. A
   stored head replays for current point binders, or when its old binder was
   nonpoint and the current binder stays nonpoint (same invocation/decl/seed).
   Old-point to current-nonpoint is explicitly left out by NoPointLoss.

## Compound endpoint warning, precisely scoped

CompoundEndpoint237 proves that a where argument `variant tag (var name)` still
uses legacy purpose3 for its lower endpoint. Two packets with the same seed,
invocation and declaration require equivalent lower capture values if both
Outputs hold in one model. A stored old packet in the actual state.plans and a
non-equivalent current lower value therefore exclude current fullHolds for that
model. This is a conditional obstruction to the proposed current-packet
completion method, NOT a demonstrated reachable/selected/stable fixture and NOT
an EvidenceNode refutation. Historical evidence replay may still be sufficient.
No language decision or further endpoint versioning was performed.

## Remaining work

Protected aggregate coverage and protected actual-binder replay need general
source invariants. The actual-head/output/child model must still be constructed
simultaneously; independently existing witnesses are not combined. In particular,
old-point/current-nonpoint actual binders and fixed compound output endpoints
need further analysis. A full source fixture is needed before calling the
compound condition a counterexample to any general target.

Independent read-only review of the parent's semantic support chain, supported
completion/head transport and acyclic historical-equation solver found their
stated scopes sound. Support/Covered is not IdCovered; a subsystem merge solution
is not a full-journal model.
