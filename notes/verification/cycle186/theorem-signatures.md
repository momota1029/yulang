# Cycle186 public theorem signatures

## GeneralNominalChildSemantic186.child_centers

```lean
theorem child_centers (first last : Plan roles)
    (seed : first.packet.context.state.seed = last.packet.context.state.seed)
    (invocation : first.packet.site.occurrence.identity = last.packet.site.occurrence.identity)
    (declaration : first.packet.declaration = last.packet.declaration)
    (clause : Clause) (member : clause ∈ first.packet.declaration.requirements)
    (signature : clause.Signature roles) (model : Assignment)
    (binders : ∀ name ∈ first.packet.declaration.inputNames,
      Same model (.source (first.binder name)) (.source (last.binder name)))
    (index : Fin (roles clause.role).arity) :
    Same model (.source ((first.childSite clause signature).center index))
      (.source ((last.childSite clause signature).center index))
```

## GeneralNominalChildSemantic186.child_centers_list

```lean
theorem child_centers_list (first last : Plan roles)
    (seed : first.packet.context.state.seed = last.packet.context.state.seed)
    (invocation : first.packet.site.occurrence.identity = last.packet.site.occurrence.identity)
    (declaration : first.packet.declaration = last.packet.declaration)
    (clause : Clause) (member : clause ∈ first.packet.declaration.requirements)
    (signature : clause.Signature roles) (model : Assignment)
    (binders : ∀ name ∈ first.packet.declaration.inputNames,
      Same model (.source (first.binder name)) (.source (last.binder name))) :
    ∀ index : Nat, Same model
      (.source (((List.ofFn (first.childSite clause signature).center)[index]?).getD 0))
      (.source (((List.ofFn (last.childSite clause signature).center)[index]?).getD 0))
```

## GeneralNominalHeadBinderCollisions186.point_binder

```lean
theorem point_binder (candidate : Plan roles) (name : Nat)
    (input : name ∉ candidate.packet.declaration.outputNames)
    (point : ((GeneralNominalPacketSupport.capture candidate.packet).inputs name).1 =
      ((GeneralNominalPacketSupport.capture candidate.packet).inputs name).2) :
    candidate.binder name = ((GeneralNominalPacketSupport.capture candidate.packet).inputs name).1
```

## GeneralNominalHeadBinderCollisions186.nonpoint_name

```lean
theorem nonpoint_name (candidate : Plan roles) (first last : Nat)
    (one : first ∉ candidate.packet.declaration.outputNames)
    (two : last ∉ candidate.packet.declaration.outputNames)
    (a : ((GeneralNominalPacketSupport.capture candidate.packet).inputs first).1 ≠
      ((GeneralNominalPacketSupport.capture candidate.packet).inputs first).2)
    (b : ((GeneralNominalPacketSupport.capture candidate.packet).inputs last).1 ≠
      ((GeneralNominalPacketSupport.capture candidate.packet).inputs last).2)
    (same : candidate.binder first = candidate.binder last) : first = last
```

## GeneralNominalHeadBinderCollisions186.point_fits

```lean
theorem point_fits (candidate : Plan roles) (name : Nat)
    (input : name ∉ candidate.packet.declaration.outputNames)
    (point : ((GeneralNominalPacketSupport.capture candidate.packet).inputs name).1 =
      ((GeneralNominalPacketSupport.capture candidate.packet).inputs name).2)
    (model : Assignment) (value : Ty)
    (fits : GeneralNominalCaptureMerges.Fits model
      ((GeneralNominalPacketSupport.capture candidate.packet).inputs name) value) :
    Equivalent value (model (candidate.binder name)).1
```

## GeneralNominalHeadBinderCollisions186.historical_coherence

```lean
theorem historical_coherence (checked : Checked registry)
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (historical candidate : Plan roles) (member : historical ∈ state.core.plans)
    (registered : candidate.input ∈ state.core.sites)
    (identity : candidate.packet.site.occurrence.identity = historical.packet.site.occurrence.identity)
    (current : candidate.packet.context = state.core.erased.current.context)
    (declaration : candidate.packet.declaration = historical.packet.declaration)
    (first last : Use) (one : first ∈ candidate.headSchema.variables) (two : last ∈ candidate.headSchema.variables)
    (oneActual : first.mode = .actual) (twoActual : last.mode = .actual)
    (oneInput : first.name ∉ candidate.packet.declaration.outputNames)
    (twoInput : last.name ∉ candidate.packet.declaration.outputNames)
    (model : Assignment) (valid : Models state model)
    (a b : Ty) (seenA : Observes model first.origin a) (seenB : Observes model last.origin b)
    (fitA : GeneralNominalCaptureMerges.Fits model ((GeneralNominalPacketSupport.capture candidate.packet).inputs first.name) a)
    (fitB : GeneralNominalCaptureMerges.Fits model ((GeneralNominalPacketSupport.capture candidate.packet).inputs last.name) b)
    (same : candidate.binder first.name = candidate.binder last.name) : Equivalent a b
```

## GeneralNominalHeadCandidateExtension186.candidate_extension_iff

```lean
theorem candidate_extension_iff (checked : Checked registry)
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (candidate : Plan roles) (registered : candidate.input ∈ state.core.sites)
    (current : candidate.packet.context = state.core.erased.current.context)
    (visible : candidate.packet.declaration ∈ registry.declarations)
    (entries : Fin count → Use)
    (present : ∀ i, entries i ∈ candidate.headSchema.variables)
    (actual : ∀ i, (entries i).mode = .actual)
    (input : ∀ i, (entries i).name ∉ candidate.packet.declaration.outputNames)
    (previous : Assignment) (valid : Models state previous)
    (linked : ∀ i, (argument candidate (entries i)).argument.endpoints.1 ∈ fullSources state ∧
      (argument candidate (entries i)).argument.endpoints.2 ∈ fullSources state ∧
      originSource (entries i).origin ∈ fullSources state) :
    (∃ extended, Models state extended ∧
      (∀ name ∈ fullSources state, extended name = previous name) ∧
      ∀ i, (argument candidate (entries i)).Holds extended) ↔
    (∀ i, ∃ value, Observes previous (entries i).origin value) ∧
    (∀ i value, Observes previous (entries i).origin value →
      GeneralNominalCaptureMerges.Fits previous
        ((GeneralNominalPacketSupport.capture candidate.packet).inputs (entries i).name) value) ∧
    (∀ i j first last, candidate.binder (entries i).name = candidate.binder (entries j).name →
      Observes previous (entries i).origin first → Observes previous (entries j).origin last → Equivalent first last)
```

## GeneralNominalHeadCandidateOverlap186.candidate_overlap

```lean
theorem candidate_overlap (checked : Checked registry)
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (candidate : Plan roles) (registered : candidate.input ∈ state.core.sites)
    (current : candidate.packet.context = state.core.erased.current.context)
    (visible : candidate.packet.declaration ∈ registry.declarations)
    (entry : Use) (present : entry ∈ candidate.headSchema.variables) (actual : entry.mode = .actual)
    (input : entry.name ∉ candidate.packet.declaration.outputNames)
    (nonpoint : ((GeneralNominalPacketSupport.capture candidate.packet).inputs entry.name).1 ≠
      ((GeneralNominalPacketSupport.capture candidate.packet).inputs entry.name).2)
    (overlap : candidate.binder entry.name ∈ GeneralNominalHeadLedgerFrame182.fullSources state)
    (model : Assignment) (valid : Models state model) :
    Same model entry.origin (.source (candidate.binder entry.name))
```

## GeneralNominalHeadCandidateSemantic186.candidate_actual

```lean
theorem candidate_actual (checked : Checked registry)
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (historical candidate : Plan roles) (member : historical ∈ state.core.plans)
    (registered : candidate.input ∈ state.core.sites)
    (identity : candidate.packet.site.occurrence.identity = historical.packet.site.occurrence.identity)
    (current : candidate.packet.context = state.core.erased.current.context)
    (declaration : candidate.packet.declaration = historical.packet.declaration)
    (entry : Use) (present : entry ∈ candidate.headSchema.variables) (actual : entry.mode = .actual)
    (model : Assignment) (valid : Models state model) :
    Same model entry.origin (.source (historical.binder entry.name))
```

## GeneralNominalHeadCandidateSemantic186.candidate_nonpoint_overlap

```lean
theorem candidate_nonpoint_overlap (checked : Checked registry)
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (historical candidate : Plan roles) (member : historical ∈ state.core.plans)
    (registered : candidate.input ∈ state.core.sites)
    (identity : candidate.packet.site.occurrence.identity = historical.packet.site.occurrence.identity)
    (current : candidate.packet.context = state.core.erased.current.context)
    (declaration : candidate.packet.declaration = historical.packet.declaration)
    (entry : Use) (present : entry ∈ candidate.headSchema.variables) (actual : entry.mode = .actual)
    (input : entry.name ∉ candidate.packet.declaration.outputNames)
    (candidateNonpoint : ((GeneralNominalPacketSupport.capture candidate.packet).inputs entry.name).1 ≠
      ((GeneralNominalPacketSupport.capture candidate.packet).inputs entry.name).2)
    (historicalNonpoint : ((GeneralNominalPacketSupport.capture historical.packet).inputs entry.name).1 ≠
      ((GeneralNominalPacketSupport.capture historical.packet).inputs entry.name).2)
    (model : Assignment) (valid : Models state model) :
    Same model entry.origin (.source (candidate.binder entry.name))
```

## GeneralNominalHeadCandidateSupport186.schemas_bounded_roots

```lean
theorem schemas_bounded_roots (queries : List Query) (origins : Nat → Origin)
    (mode : Mode) (offset : Nat)
    (known : ∀ index, offset ≤ index → index < offset + queries.length → originSource (origins index) ∈ names) :
    Roots (schemas queries origins mode offset) names
```

## GeneralNominalHeadCandidateSupport186.normalized_length

```lean
theorem normalized_length (patterns : List GeneralDeclarationPatterns.Pattern) :
    (GeneralDeclarationPatterns.normalizeArgs patterns).length = patterns.length
```

## GeneralNominalHeadCandidateSupport186.head_roots

```lean
theorem head_roots (plan : Plan roles)
    (aligned : plan.packet.declaration.role = plan.input.occurrence.demand.role) :
    Roots plan.headSchema (List.ofFn plan.input.center)
```

## GeneralNominalHeadCandidateSupport186.current_source

```lean
theorem current_source (state : State roles) (member : name ∈ GeneralNominalState.sources state.core.erased.current.context.state) :
    name ∈ fullSources state
```

## GeneralNominalHeadCandidateSupport186.registered_center

```lean
theorem registered_center (state : State roles) (site : Site roles)
    (registered : site ∈ state.core.sites) (member : name ∈ List.ofFn site.center) :
    name ∈ fullSources state
```

## GeneralNominalHeadCandidateSupport186.candidate_origin

```lean
theorem candidate_origin (state : State roles) (candidate : Plan roles)
    (registered : candidate.input ∈ state.core.sites)
    (aligned : candidate.packet.declaration.role = candidate.input.occurrence.demand.role)
    (entry : Use) (present : entry ∈ candidate.headSchema.variables) :
    originSource entry.origin ∈ fullSources state
```

## GeneralNominalHeadCandidateSupport186.singleton_endpoints

```lean
theorem singleton_endpoints (state : State roles) (candidate : Plan roles)
    (current : candidate.packet.context = state.core.erased.current.context)
    (name : Nat) (bounds : GeneralSourceState.Interval)
    (singleton : GeneralNominalAllocation.occurrences candidate.packet.bindings name = [bounds]) :
    ((GeneralNominalPacketSupport.capture candidate.packet).inputs name).1 ∈ fullSources state ∧
      ((GeneralNominalPacketSupport.capture candidate.packet).inputs name).2 ∈ fullSources state
```

## GeneralNominalHeadCandidateSupport186.current_capture_separate

```lean
theorem current_capture_separate
    (reachable : B4TargetV6.Reachable (GeneralNominalCenteredHeadWFBoundary.boundary roles) registry root state)
    (packet : GeneralNominalSaturationState.Packet roles)
    (current : packet.context = state.core.erased.current.context)
    (high : 7 ≤ purpose) (name : Nat) :
    fresh state.core.erased.current.context.state.seed invocation declaration purpose owner position ≠
      ((GeneralNominalPacketSupport.capture packet).inputs name).1 ∧
    fresh state.core.erased.current.context.state.seed invocation declaration purpose owner position ≠
      ((GeneralNominalPacketSupport.capture packet).inputs name).2
```

## GeneralNominalHeadCandidateSupport186.nonpoint_binder_endpoints_separate

```lean
theorem nonpoint_binder_endpoints_separate
    (reachable : B4TargetV6.Reachable (GeneralNominalCenteredHeadWFBoundary.boundary roles) registry root state)
    (candidate : Plan roles)
    (current : candidate.packet.context = state.core.erased.current.context)
    (name : Nat) (input : name ∉ candidate.packet.declaration.outputNames)
    (nonpoint : ((GeneralNominalPacketSupport.capture candidate.packet).inputs name).1 ≠
      ((GeneralNominalPacketSupport.capture candidate.packet).inputs name).2)
    (other : Nat) :
    candidate.binder name ≠ ((GeneralNominalPacketSupport.capture candidate.packet).inputs other).1 ∧
      candidate.binder name ≠ ((GeneralNominalPacketSupport.capture candidate.packet).inputs other).2
```

## GeneralNominalHeadConservativeExtension186.lower_mem

```lean
theorem lower_mem (candidate : Plan roles) (entries : Fin count → Use) (index : Fin count) :
    ((GeneralNominalPacketSupport.capture candidate.packet).inputs (entries index).name).1 ∈
      captureEndpoints candidate entries
```

## GeneralNominalHeadConservativeExtension186.upper_mem

```lean
theorem upper_mem (candidate : Plan roles) (entries : Fin count → Use) (index : Fin count) :
    ((GeneralNominalPacketSupport.capture candidate.packet).inputs (entries index).name).2 ∈
      captureEndpoints candidate entries
```

## GeneralNominalHeadConservativeExtension186.conservative_extension_iff

```lean
theorem conservative_extension_iff (checked : Checked registry)
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (candidate : Plan roles) (registered : candidate.input ∈ state.core.sites)
    (aligned : candidate.packet.declaration.role = candidate.input.occurrence.demand.role)
    (current : candidate.packet.context = state.core.erased.current.context)
    (visible : candidate.packet.declaration ∈ registry.declarations)
    (entries : Fin count → Use)
    (present : ∀ i, entries i ∈ candidate.headSchema.variables)
    (actual : ∀ i, (entries i).mode = .actual)
    (input : ∀ i, (entries i).name ∉ candidate.packet.declaration.outputNames)
    (previous : Assignment) (valid : Models state previous) :
    (∃ extended, Models state extended ∧
      (∀ name ∈ support state candidate entries, extended name = previous name) ∧
      ∀ i, (argument candidate (entries i)).Holds extended) ↔
    (∀ i, ∃ value, Observes previous (entries i).origin value) ∧
    (∀ i value, Observes previous (entries i).origin value →
      GeneralNominalCaptureMerges.Fits previous
        ((GeneralNominalPacketSupport.capture candidate.packet).inputs (entries i).name) value) ∧
    (∀ i j first last, candidate.binder (entries i).name = candidate.binder (entries j).name →
      Observes previous (entries i).origin first → Observes previous (entries j).origin last → Equivalent first last)
```

## GeneralNominalHeadEquationExtension186.uses_mem

```lean
theorem uses_mem (candidate : Plan roles) (index : Fin candidate.headSchema.variables.length) :
    uses candidate index ∈ candidate.headSchema.variables
```

## GeneralNominalHeadEquationExtension186.uses_cover

```lean
theorem uses_cover (candidate : Plan roles) (entry : Use)
    (member : entry ∈ candidate.headSchema.variables) : ∃ index, uses candidate index = entry
```

## GeneralNominalHeadEquationExtension186.tests_frame

```lean
theorem tests_frame (candidate : Plan roles) (registered : candidate.input ∈ state.core.sites)
    (aligned : candidate.packet.declaration.role = candidate.input.occurrence.demand.role)
    (previous extended : Assignment)
    (kept : ∀ name ∈ support state candidate (uses candidate), extended name = previous name)
    (test) (member : test ∈ candidate.headSchema.tests) :
    Head previous test.1 test.2 ↔ Head extended test.1 test.2
```

## GeneralNominalHeadEquationExtension186.head_equations_extension_iff

```lean
theorem head_equations_extension_iff (checked : Checked registry)
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (candidate : Plan roles) (registered : candidate.input ∈ state.core.sites)
    (aligned : candidate.packet.declaration.role = candidate.input.occurrence.demand.role)
    (current : candidate.packet.context = state.core.erased.current.context)
    (visible : candidate.packet.declaration ∈ registry.declarations)
    (finished : Finished (GeneralNominalQueryProvenance183.headInspection candidate))
    (previous : Assignment) (valid : Models state previous) :
    (∃ extended, Models state extended ∧
      (∀ name ∈ support state candidate (uses candidate), extended name = previous name) ∧
      GeneralNominalCenteredHeadOutputs.HeadEquations candidate extended) ↔ Compatible candidate previous
```

## GeneralNominalHeadFrameExtension186.frame_finished

```lean
theorem frame_finished (frame : Frame registry state.core focus key candidate) :
    GeneralNominalRecursiveInspection.Finished (GeneralNominalQueryProvenance183.headInspection candidate)
```

## GeneralNominalHeadFrameExtension186.frame_aligned

```lean
theorem frame_aligned (frame : Frame registry state.core focus key candidate) :
    candidate.packet.declaration.role = candidate.input.occurrence.demand.role
```

## GeneralNominalHeadFrameExtension186.frame_extension_iff

```lean
theorem frame_extension_iff (checked : Checked registry)
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (frame : Frame registry state.core focus key candidate)
    (previous : Assignment) (valid : Models state previous) :
    (∃ extended, Models state extended ∧
      (∀ name ∈ support state candidate (uses candidate), extended name = previous name) ∧
      HeadEquations candidate extended) ↔ Compatible candidate previous
```

## GeneralNominalHeadIdentityCenters186.trace_registered_binders

```lean
theorem trace_registered_binders
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (first last : Plan roles) (one : first ∈ state.core.plans) (two : last ∈ state.core.plans)
    (declaration : first.packet.declaration = last.packet.declaration)
    (model : Assignment) (valid : Models state model)
    (centers : CentersSame model first.input last.input)
    (name : Nat) (named : name ∈ first.packet.declaration.inputNames) :
    Same model (.source (first.binder name)) (.source (last.binder name))
```

## GeneralNominalHeadIdentityCenters186.trace_registered_identity_centers_same

```lean
theorem trace_registered_identity_centers_same (checked : Checked registry)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (first last : Site roles) (one : first ∈ state.core.sites) (two : last ∈ state.core.sites)
    (identity : first.occurrence.identity = last.occurrence.identity)
    (model : Assignment) (valid : Models state model) : CentersSame model first last
```

## GeneralNominalHeadIdentityCenters186.registered_identity_centers_same

```lean
theorem registered_identity_centers_same (checked : Checked registry)
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (first last : Site roles) (one : first ∈ state.core.sites) (two : last ∈ state.core.sites)
    (identity : first.occurrence.identity = last.occurrence.identity)
    (model : Assignment) (valid : Models state model) : CentersSame model first last
```

## GeneralNominalHeadIdentityCenters186.registered_identity_binders_same

```lean
theorem registered_identity_binders_same (checked : Checked registry)
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (first last : Plan roles) (one : first ∈ state.core.plans) (two : last ∈ state.core.plans)
    (identity : first.packet.site.occurrence.identity = last.packet.site.occurrence.identity)
    (declaration : first.packet.declaration = last.packet.declaration)
    (name : Nat) (named : name ∈ first.packet.declaration.inputNames)
    (model : Assignment) (valid : Models state model) :
    Same model (.source (first.binder name)) (.source (last.binder name))
```

## GeneralNominalHeadIdentityInduction186.centers_self

```lean
theorem centers_self (model : Assignment) (site : Site roles) : CentersSame model site site
```

## GeneralNominalHeadIdentityInduction186.trace_identity_centers

```lean
theorem trace_identity_centers (checked : Checked registry)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (model : Assignment)
    (transfer : ∀ first ∈ state.core.plans, ∀ last ∈ state.core.plans,
      first.packet.declaration = last.packet.declaration →
      CentersSame model first.input last.input →
      ∀ name ∈ first.packet.declaration.inputNames,
        Same model (.source (first.binder name)) (.source (last.binder name)))
    (first last : Site roles) (one : first ∈ state.core.sites) (two : last ∈ state.core.sites)
    (identity : first.occurrence.identity = last.occurrence.identity) :
    CentersSame model first last
```

## GeneralNominalHeadRevisitExtension186.compatible_iff_bounds

```lean
theorem compatible_iff_bounds (checked : Checked registry)
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (historical candidate : Plan roles) (member : historical ∈ state.core.plans)
    (registered : candidate.input ∈ state.core.sites)
    (identity : candidate.packet.site.occurrence.identity = historical.packet.site.occurrence.identity)
    (current : candidate.packet.context = state.core.erased.current.context)
    (declaration : candidate.packet.declaration = historical.packet.declaration)
    (model : Assignment) (valid : Models state model) :
    Compatible candidate model ↔ BoundsFit candidate model
```

## GeneralNominalHeadRevisitExtension186.revisit_extension_iff_bounds

```lean
theorem revisit_extension_iff_bounds (checked : Checked registry)
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (historical candidate : Plan roles) (member : historical ∈ state.core.plans)
    (frame : Frame registry state.core focus key candidate)
    (identity : candidate.packet.site.occurrence.identity = historical.packet.site.occurrence.identity)
    (declaration : candidate.packet.declaration = historical.packet.declaration)
    (model : Assignment) (valid : Models state model) :
    (∃ extended, Models state extended ∧
      (∀ name ∈ support state candidate (uses candidate), extended name = model name) ∧
      HeadEquations candidate extended) ↔ BoundsFit candidate model
```

## GeneralNominalHeadSchemaNames186.schema_actual

```lean
theorem schema_actual (query : Query) (origin : Origin) (entry : Use)
    (present : entry ∈ (schema query origin .actual).variables) : entry.mode = .actual
```

## GeneralNominalHeadSchemaNames186.schemas_actual

```lean
theorem schemas_actual (queries : List Query) (origins : Nat → Origin) (offset : Nat)
    (entry : Use) (present : entry ∈ (schemas queries origins .actual offset).variables) :
    entry.mode = .actual
```

## GeneralNominalHeadSchemaNames186.head_actual

```lean
theorem head_actual (plan : Plan roles) (entry : Use) (present : entry ∈ plan.headSchema.variables) :
    entry.mode = .actual
```

## GeneralNominalHeadSchemaNames186.head_input

```lean
theorem head_input (plan : Plan roles) (entry : Use) (present : entry ∈ plan.headSchema.variables) :
    entry.name ∈ plan.packet.declaration.inputNames
```

## GeneralNominalHeadSchemaNames186.input_not_output

```lean
theorem input_not_output (plan : Plan roles) (name : Nat)
    (input : name ∈ plan.packet.declaration.inputNames) : name ∉ plan.packet.declaration.outputNames
```

## GeneralNominalHeadSchemaNames186.head_not_output

```lean
theorem head_not_output (plan : Plan roles) (entry : Use) (present : entry ∈ plan.headSchema.variables) :
    entry.name ∉ plan.packet.declaration.outputNames
```

## GeneralNominalHeadSchemaSemantic186.related_symm

```lean
theorem related_symm (related : Related model first last) : Related model last first
```

## GeneralNominalHeadSchemaSemantic186.related_holds

```lean
theorem related_holds (related : Related model first last)
    (valid : Holds model term first) : Holds model term last
```

## GeneralNominalHeadSchemaSemantic186.structural_related

```lean
theorem structural_related (related : Related model first last) (shape : GeneralNormalizedObservation.Shape)
    (index : Nat) : Related model (.structural first shape index) (.structural last shape index)
```

## GeneralNominalHeadSchemaSemantic186.nominal_related

```lean
theorem nominal_related (related : Related model first last) (name index : Nat) :
    Related model (.nominal first name index) (.nominal last name index)
```

## GeneralNominalHeadSchemaSemantic186.schema_correspondence

```lean
theorem schema_correspondence (query : Query) (first last : Origin) (mode : Mode)
    (related : Related model first last) (entry : Use)
    (member : entry ∈ (schema query first mode).variables) :
    ∃ other ∈ (schema query last mode).variables,
      entry.name = other.name ∧ entry.mode = other.mode ∧ Related model entry.origin other.origin
```

## GeneralNominalHeadSchemaSemantic186.schemas_correspondence

```lean
theorem schemas_correspondence (queries : List Query) (first last : Nat → Origin) (mode : Mode)
    (index : Nat) (related : ∀ i, Related model (first i) (last i)) (entry : Use)
    (member : entry ∈ (schemas queries first mode index).variables) :
    ∃ other ∈ (schemas queries last mode index).variables,
      entry.name = other.name ∧ entry.mode = other.mode ∧ Related model entry.origin other.origin
```

## GeneralNominalHeadSchemaSemantic186.head_correspondence

```lean
theorem head_correspondence (first last : Plan roles)
    (declaration : first.packet.declaration = last.packet.declaration)
    (constructors : first.packet.context.state.constructors = last.packet.context.state.constructors)
    (interpretation : first.packet.context.interpretation = last.packet.context.interpretation)
    (centers : ∀ index : Nat,
      Same model (.source ((List.ofFn first.input.center)[index]?.getD 0))
        (.source ((List.ofFn last.input.center)[index]?.getD 0)))
    (entry : Use) (member : entry ∈ first.headSchema.variables) :
    ∃ other ∈ last.headSchema.variables,
      entry.name = other.name ∧ entry.mode = other.mode ∧ Related model entry.origin other.origin
```

## GeneralNominalHeadSchemaSemantic186.input_use

```lean
theorem input_use (plan : Plan roles)
    (finished : Finished (GeneralNominalQueryProvenance183.headInspection plan))
    (name : Nat) (named : name ∈ plan.packet.declaration.inputNames) :
    ∃ origin, (⟨name,origin,.actual⟩ : Use) ∈ plan.headSchema.variables
```

## GeneralNominalHeadSchemaSemantic186.binder_same

```lean
theorem binder_same (first last : Plan roles)
    (declaration : first.packet.declaration = last.packet.declaration)
    (constructors : first.packet.context.state.constructors = last.packet.context.state.constructors)
    (interpretation : first.packet.context.interpretation = last.packet.context.interpretation)
    (centers : ∀ index : Nat,
      Same model (.source ((List.ofFn first.input.center)[index]?.getD 0))
        (.source ((List.ofFn last.input.center)[index]?.getD 0)))
    (one : first.SchemaHolds first.headSchema model)
    (two : last.SchemaHolds last.headSchema model)
    (finished : Finished (GeneralNominalQueryProvenance183.headInspection first))
    (name : Nat) (named : name ∈ first.packet.declaration.inputNames) :
    Same model (.source (first.binder name)) (.source (last.binder name))
```

## GeneralNominalHeadTestSemantic186.related_head

```lean
theorem related_head (related : Related model first last) (valid : Head model first test) :
    Head model last test
```

## GeneralNominalHeadTestSemantic186.schema_tests

```lean
theorem schema_tests (query : Query) (first last : Origin) (mode : Mode)
    (related : Related model first last) (test : Origin × Test)
    (member : test ∈ (schema query first mode).tests) :
    ∃ other ∈ (schema query last mode).tests,
      test.2 = other.2 ∧ Related model test.1 other.1
```

## GeneralNominalHeadTestSemantic186.schemas_tests

```lean
theorem schemas_tests (queries : List Query) (first last : Nat → Origin) (mode : Mode)
    (offset : Nat) (related : ∀ index, Related model (first index) (last index))
    (test : Origin × Test) (member : test ∈ (schemas queries first mode offset).tests) :
    ∃ other ∈ (schemas queries last mode offset).tests,
      test.2 = other.2 ∧ Related model test.1 other.1
```

## GeneralNominalHeadTestSemantic186.head_tests

```lean
theorem head_tests (first last : Plan roles)
    (declaration : first.packet.declaration = last.packet.declaration)
    (constructors : first.packet.context.state.constructors = last.packet.context.state.constructors)
    (interpretation : first.packet.context.interpretation = last.packet.context.interpretation)
    (centers : ∀ index : Nat,
      Same model (.source ((List.ofFn first.input.center)[index]?.getD 0))
        (.source ((List.ofFn last.input.center)[index]?.getD 0)))
    (test : Origin × Test) (member : test ∈ first.headSchema.tests) :
    ∃ other ∈ last.headSchema.tests,
      test.2 = other.2 ∧ Related model test.1 other.1
```

## GeneralNominalHeadTestSemantic186.candidate_tests

```lean
theorem candidate_tests (checked : Checked registry)
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (historical candidate : Plan roles) (member : historical ∈ state.core.plans)
    (registered : candidate.input ∈ state.core.sites)
    (identity : candidate.packet.site.occurrence.identity = historical.packet.site.occurrence.identity)
    (current : candidate.packet.context = state.core.erased.current.context)
    (declaration : candidate.packet.declaration = historical.packet.declaration)
    (model : Assignment) (valid : Models state model)
    (test : Origin × Test) (present : test ∈ candidate.headSchema.tests) : Head model test.1 test.2
```
