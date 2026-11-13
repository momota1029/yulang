# Cycle169 next bridge: ground meanings, current observations, and dictionary coverage

Status: read-only proof-obligation handoff, 2026-11-13. Sources: fresh integration `b95d31b190`, `GeneralNominalFiniteMeaning`, `GeneralNominalGroundAccessibility`, `GeneralNominalGroundProduction`, `GeneralNominalGroundExamples`, and `notes/design/2026-11-14-ground-root-production.md`; cycle169 NamedTree/FiniteCoverage. This note proves no new theorem and changes no semantics.

## 1. Do not identify these three kinds of evidence

1. `GeneralNominalFiniteMeaning.At model mode origin value` is a **semantic** observation/readback: some `Observes` exists, and all observations approximate the value in the indicated direction. It is indexed by one model.
2. `GeneralDictionaryObservedFiniteRequests.Tree state slot query` is an **actual snapshot shape certificate**. A scalar constructor requires `state.view.heads slot = .scalar base`; a nominal constructor requires an actual recorded descriptor and exact point-slot parameters, recursively. Its `Observed` wrapper additionally locates each request target at `state.base.source slot` and matches translated normalized syntax.
3. `GeneralDictionary169FiniteCoverage.Child coverage` is a relation between **selected dictionary occurrence nodes** in one fixed Shared state. `Acc` for that relation is not accessibility of the operational state transition relation.

None of the new Astra theorems supplies an automatic conversion between these three. In particular, semantic equivalence to a finite constructor value does not create a descriptor slot, and operational termination does not by itself establish acyclicity of an independently chosen dictionary dependency graph.

## 2. Existing signatures and what they actually supply

### FiniteMeaning

- `project_value (test) (canonical : TestCanonical test) (values) (meaning : At model .actual root (build test values)) (index)` returns `At model .actual (project root test index) (values index)`.
- `followed_readback (path : Follows root term endpoint part) (canonical : Canonical term) (values) (meaning : At model .actual root (denote values term))` returns `Canonical part ∧ At model .actual endpoint (denote values part)`.
- `followed_closed path (closed : term.leaves = [])` returns `part.leaves = []`.

These supply finite semantic subreadbacks **after** a syntax-aligned `Follows` path is provided. They do not extract that path from a live inspection report or prove an actual descriptor lookup. `ClosedTerm context pattern term` additionally records normalized translation=quotation, no leaves, and canonicality, not snapshot representation.

### GroundProduction

- `capture_value packet model valid input usable meaning` needs packet.Holds, a name outside outputNames, `Usable packet name origin`, and exact `At` at that origin. It returns the common `CaptureValue` and transfers that readback across every usable representative of the same binder.
- `argument_contained ... (meaning : ArgumentValue packet model clause signature index value)` returns semantic `Fits` of the emitted child interval.
- `argument_retained ... meaning recorded` additionally returns exact `At` only when the actual Shared child-site entry retains an origin.
- `child_inputs packet coherence model valid clause present signature length meanings` returns `GroundAccessibility.Inputs context model (SharedEmission.childSite packet (clauseChild ...)) labels` from per-position closed terms and ArgumentValue. It is a real-emitter semantic theorem, not selected-child dictionary existence.
- `recovered_inputs state model valid known` preserves those semantic Inputs across the existing recover operation. Missing-origin recovery still needs the operation's EndpointEqual condition. It does not select a center of a strict interval.

### The residual producer premise remains residual

`GroundCaptureFactorization roles registry context` still requires, for each installable packet with the **ActualInspectionSteps.PacketGuard**, nonempty requirements, compatible metadata, current/packet model, and Inputs labels, one substitution with:

- instantiated-head Paterson mass at most input-label mass;
- closed quoted child labels of exact arity;
- each child's `ArgumentValue`.

`packet_production : GroundCaptureFactorization ... → GroundPacketProduction ...` proves emitted-site meanings from this. It does not prove factorization. Deriving factorization is Astra's termination/producer work, not a new assumption that closes dot's Evidence boundary.

### Accessibility is for the stronger actual-inspection relation

The existing strongest result is:

```lean
GeneralNominalGroundProduction.ground_accessible_of_capture_factorization
  (checked : Checked registry)
  (source : InitialSource registry context root)
  (point : GeneralNominalActualBudget.PointSource context root)
  (ground : GroundRoots context root rootLabels)
  (factorization : GroundCaptureFactorization roles registry context) :
  Acc (fun next current =>
    GeneralNominalActualInspectionSteps.Step registry root current next)
    (GeneralNominalSupport.initial context root)
```

`ActualInspectionSteps.PacketGuard` is Shared PacketGuard **plus** actual inspected-position Safe and AlternativesSafe. `step_shared` converts ActualInspection Step to Shared Step, not conversely. Accessibility of this restricted relation must not be reported as accessibility of all Shared transitions. Likewise Shared SourceFormed alone does not provide an ActualInspection trace.

## 3. Exact consumers on the Evidence side

Current cycle169 has:

```lean
GeneralDictionary169FiniteCoverage.accessible_tree
  (coverage : Coverage registry state domain)
  (focus : Subtype domain)
  (accessible : Acc (Child coverage) focus) :
  ∃ payload, GeneralDictionaryMixed168Tree.MixedTree registry state focus.val payload
```

`Coverage.node` picks a local Node for every domain member; `Coverage.closed` proves all of its actual chosen children remain in the domain. Node currently has only recorded+Relocates, scalar, and spine constructors. It **does not include** the new named leaf. `uniform_dictionary` then puts one payload outside the forall-model quantifier, using SourceFormed.

`GeneralDictionary169NamedTree.current_evidence` already interprets recursive recorded/named/mixed certificates for every current model, but there is no general NamedTree analogue of FiniteCoverage's local-node/Acc assembler yet. Such an additive assembler is mechanical preparatory work; it would not discharge local coverage or accessibility.

For an unrecorded named leaf, `GeneralDictionary169NamedLeaf.LeafShape` still specifically requires terminal requirements, scalar input with real slot/head/query/arguments, no input binders, RootDefined, and Observed for the **actual** requests computed from the actual report bindings. It is not an arbitrary ground-input leaf theorem.

## 4. Concrete next proof obligations, in dependency order

### A. Current structural shape, not semantic value alone

For a restricted source-normalized family, prove actual source slot/descriptor witnesses for each translated request, then construct `ObservedFiniteRequests.Tree`. A useful target shape (schematic only, not an existing theorem) is:

```lean
-- Must explicitly identify the chosen finite request syntax and current slots.
(current structural lookup/projection facts for every generated request) →
GeneralDictionaryObservedFiniteRequests.Observed state interpretation
  (GeneralNominalMaterialization.requests state registry occurrence declaration checked
    (GeneralNominalRecursiveInspection.bindings state
      (GeneralNominalRecursiveCandidates.report context declaration bounds)))
```

FiniteMeaning's semantic `At` may justify model interpretation of these facts, but cannot replace the actual lookup hypotheses. A general theorem that all reachable Stable states expose such descriptors would need a genuine observation-completeness argument against actual administrative actions. No such theorem was identified in the inspected new modules.

The current ObservedFiniteRequests.Tree itself supports scalar and arbitrary finite nominal type-argument trees, **not structural pair/record/variant constructors**. The new GroundExamples root is a structural pair. Do not reuse the nominal-only certificate as if it covered that root. Supporting those shapes requires a separately checked structural certificate/interpreter, or a recorded nonterminal node route after a real installation.

### B. Local node coverage at a chosen current occurrence

For recorded nodes, obtain actual packet membership and the exact occurrence, then derive source-ID/seed/report/schema agreement needed by `Recorded168Relocation.Relocates`. Ground `Inputs` is semantic and does not establish report/schema equality. Cycle169 ordinary persistence covers subsequent ordinary extensions only, not arbitrary descriptor refresh.

For packet-free nodes, derive the concrete leaf shape from A (or existing scalar/spine shape). Stable does not force every terminal packet to be recorded: the named-output initial fixture is already a concrete stable counterexample to old MixedTree coverage. The new named constructor repairs that specific certificate gap, not universal coverage.

Then prove the selected key/ordered children match the constructed current Instance via `GeneralDictionary169Selected.relocated_selected` or the underlying `SelectedInstanceCoherence.instance_selected`. These use actual FeedbackK2.Local selected at the **same occurrence**. A separate justification is still needed that the intended final boundary's Local/Unique premises give that judgment under the current guard discipline; do not substitute a legacy classifier by name.

### C. Mixed-Node Acc obligation now discharged by CoverageAccessible; Named analogue remains open. Chosen-child accessibility in a fixed final state

`GroundAccessibility.sites_bounded` gives, along an ActualInspection trace and for each surviving final model and stored site, **some** finite labels and literal ancestry depth satisfying `depth + mass labels ≤ mass rootLabels`. Labels may depend on model/state/site. This is not yet a uniform chosen-Node graph ranking.

A possible follow-on requires:

1. every chosen recorded child edge really is the literal packet child edge (`InvocationAncestry.child_identity` supplies one-step literal allocator ancestry);
2. chosen packet children are in the intended domain and remain registered/generated;
3. one coherent depth/rank assignment along those chosen edges, or a bound on **every** chosen path. Existing `sites_bounded` gives an existential depth per site; uniqueness/coherence of ancestry depth must be proved before treating it as a decreasing rank;
4. no unproved identification of literal emitted occurrences with aliased occurrences;
5. packet-free leaf cases have zero selected children.

Only after those obligations can a rank argument yield `Acc (FiniteCoverage.Child coverage) focus` (or the future named analogue). The operational Acc theorem alone is not this argument. A final-state model witness would also need to be explicit if the ranking construction extracts model-dependent labels; otherwise the reasoning risks a vacuous all-model premise.

## 5. Best bounded next experiment

Use a small actual **current observed** named/scalar or nominal fixture first. The existing named-output initial fixture is already source-formed, Shared-stable and inhabited, but its finite certificate is one node. A useful extension would establish a real installed parent with a named-output leaf and a concrete current observation certificate, showing the new recursive NamedTree branch in a nonterminal execution. It must preserve the I26 guard and prove actual packet membership/relocation, not assume parent Evidence.

Do not call the new GroundExamples branching root such an execution: its `accessible` still assumes GroundCaptureFactorization, and the source equation fixing reserved root identity2 to a pair does not by itself allocate a structural observation slot. `both_positions` proves semantic projection readbacks, not a successful packet installation or dictionary.

This plan leaves general V5 evidenceNode, all-selected coverage, arbitrary refresh transport, and termination factorization open. No specification question or guard repair is established by this read-only pass.

## 6. Historical proposal, superseded by verified late update. Stronger fixed-journal route found on final inspection

There is a simpler candidate for **dictionary** accessibility that does not need the unfinished ground producer. This is a proof plan, not a theorem proved in cycle169.

Existing exact ingredients:

- `GeneralNominalPatersonLineage.emitted_clause (packet) (child) (member : child ∈ packet.children)` yields a requirement clause/signature with `child = GeneralNominalFeedbackSites.clauseChild packet clause signature`. It does not require declaration visibility.
- `GeneralNominalIdentities.source_above_invocation (seed) (key)` proves `key.1 < source seed key`.
- Thus literal packet children should satisfy `packet.site.occurrence.identity < child.identity` by emitted_clause and the existing allocator definition. This is not an alias relation.
- `InvocationAncestry.child_identity` is also available when declaration visibility is known, and `seed_trace` aligns the seed along ActualInspection traces. They are not needed for the simpler numeric argument.
- No general uniqueness-of-depth theorem for `GeneralNominalInvocationAncestry.AtDepth` was found in the inspected modules. The similarly named `ValueDepth.AtDepth` and `DownstreamDepth.AtDepth` are different support-depth predicates and must not be substituted.

For a **fixed finite journal** J, let M be the maximum of the identities of the parent occurrences of packets in J (default0). Define the proposed rank on *all* occurrences by:

```text
rank(o) = (M + 1) - o.identity
```

For every chosen `Child coverage child parent` edge, the parent's Node cannot be scalar/spine, since their children are empty. It must be a recorded packet in J, giving `parent.identity ≤ M`. The literal child inequality gives `parent.identity < child.identity`. Truncated subtraction therefore gives `rank(child) < rank(parent)`, even if the child's identity exceeds M. This does not require the entire domain to be finite or a model witness. Packet-free leaves may have arbitrary identities; they have no outgoing edges.

The potential new signature is consequently stronger than a ground-conditional bridge:

```lean
-- Proposed, not yet implemented or checked:
-- theorem coverage_accessible
--   (coverage : GeneralDictionary169FiniteCoverage.Coverage registry state domain)
--   (focus : Subtype domain) :
--   Acc (GeneralDictionary169FiniteCoverage.Child coverage) focus
```

Then `accessible_tree` would no longer need caller-supplied Acc when Coverage is present. An analogous local Node type that adds the new named terminal leaf would have the same argument, since named leaves also have zero children.

Crucially this still does **not** derive Coverage from Stable/Reachable, prove current Relocates after arbitrary refresh, or prove operational termination. The bound M depends on one already-fixed finite journal; it cannot bound journals along an unbounded execution. GroundCaptureFactorization remains relevant to Astra's operational theorem, but may be unnecessary for this narrower dictionary assembly obligation. This is the recommended first bounded proof to attempt next, before taking on the much larger semantic-to-current-observation bridge.

### Cycle169 late verification update

The fixed-journal route in §6 was subsequently implemented and verified in the additive module `GeneralDictionary169CoverageAccessible`: `packet_child_above`, `child_rank`, `coverage_accessible`, `covered_tree`, `covered_dictionary`. The structural accessibility result needs Coverage alone, not SourceFormed or a model. The direct emitter inversion avoids new dependencies on the Astra ground modules. Consequently §6's proposed signature is now proved for the old Mixed Node Coverage. Earlier sections' externally supplied Acc obligation is removed for this precise certificate type, not for arbitrary named/local graphs or operational transitions. Local Coverage existence and the actual-observation/relocation obligations remain open. The named analogue is still a next step.
