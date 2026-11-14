# Cycle184 public theorem signatures

Auxiliary frame/provenance/coherence/conditional readback results only. Full implicit quantifiers are in public-types.txt.

## GeneralNominalCandidateCoverage184

```lean
theorem registered_head_use
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (plan : Plan roles) (registered : plan ∈ state.plans) (name : Nat)
    (named : name ∈ plan.packet.declaration.inputNames) :
    ∃ origin : Origin, (⟨name,origin,.actual⟩ : GeneralNominalMaterialization.Use) ∈ plan.headSchema.variables
```

```lean
theorem candidate_input_readback (checked : Checked registry)
    (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (historical candidate : Plan roles) (member : historical ∈ state.plans)
    (registered : candidate.input ∈ state.sites)
    (same : candidate.packet.site.occurrence = historical.packet.site.occurrence)
    (current : candidate.packet.context = state.erased.current.context)
    (declaration : candidate.packet.declaration = historical.packet.declaration)
    (name : Nat) (named : name ∈ candidate.packet.declaration.inputNames) :
    ∃ origin : Origin, (⟨name,origin,.actual⟩ : GeneralNominalMaterialization.Use) ∈ candidate.headSchema.variables ∧
      ∀ model, Models state model → Same model origin (.source (historical.binder name))
```

```lean
theorem candidate_nonpoint_readback (checked : Checked registry)
    (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (historical candidate : Plan roles) (member : historical ∈ state.plans)
    (registered : candidate.input ∈ state.sites)
    (same : candidate.packet.site.occurrence = historical.packet.site.occurrence)
    (current : candidate.packet.context = state.erased.current.context)
    (declaration : candidate.packet.declaration = historical.packet.declaration)
    (name : Nat) (named : name ∈ candidate.packet.declaration.inputNames)
    (input : name ∉ candidate.packet.declaration.outputNames)
    (candidateNonpoint : ((GeneralNominalPacketSupport.capture candidate.packet).inputs name).1 ≠
      ((GeneralNominalPacketSupport.capture candidate.packet).inputs name).2)
    (historicalNonpoint : ((GeneralNominalPacketSupport.capture historical.packet).inputs name).1 ≠
      ((GeneralNominalPacketSupport.capture historical.packet).inputs name).2) :
    ∃ origin : Origin, (⟨name,origin,.actual⟩ : GeneralNominalMaterialization.Use) ∈ candidate.headSchema.variables ∧
      ∀ model, Models state model → Same model origin (.source (candidate.binder name))
```

## GeneralNominalCenterCoherence184

```lean
theorem binder_equal (first last : Plan roles)
    (seed : first.packet.context.state.seed = last.packet.context.state.seed)
    (invocation : first.packet.site.occurrence.identity = last.packet.site.occurrence.identity)
    (declaration : first.packet.declaration = last.packet.declaration) (name : Nat)
    (inputs : (GeneralNominalPacketSupport.capture first.packet).inputs name =
      (GeneralNominalPacketSupport.capture last.packet).inputs name) :
    first.binder name = last.binder name
```

```lean
theorem emitted_equal (first last : Plan roles)
    (seed : first.packet.context.state.seed = last.packet.context.state.seed)
    (invocation : first.packet.site.occurrence.identity = last.packet.site.occurrence.identity)
    (declaration : first.packet.declaration = last.packet.declaration)
    (clause position : Nat) (pattern : GeneralDeclarationPatterns.Pattern)
    (inputs : GeneralDeclarationDemands.inputInterval (GeneralNominalPacketSupport.capture first.packet)
        firstAllocated pattern =
      GeneralDeclarationDemands.inputInterval (GeneralNominalPacketSupport.capture last.packet)
        lastAllocated pattern) :
    first.emittedCenter clause position pattern = last.emittedCenter clause position pattern
```

```lean
theorem child_center_equal (first last : Plan roles)
    (seed : first.packet.context.state.seed = last.packet.context.state.seed)
    (invocation : first.packet.site.occurrence.identity = last.packet.site.occurrence.identity)
    (declaration : first.packet.declaration = last.packet.declaration)
    (clause : Clause) (signature : clause.Signature roles)
    (index : Fin (roles clause.role).arity)
    (arguments : ((first.childSite clause signature).occurrence.demand.arguments index) =
      ((last.childSite clause signature).occurrence.demand.arguments index)) :
    (first.childSite clause signature).center index = (last.childSite clause signature).center index
```

## GeneralNominalChildCoherence184

```lean
theorem producer_ids (first last : Plan roles)
    (seed : first.packet.context.state.seed = last.packet.context.state.seed)
    (one two : Clause) (oneSignature : one.Signature roles) (twoSignature : two.Signature roles)
    (same : (first.childSite one oneSignature).occurrence.identity =
      (last.childSite two twoSignature).occurrence.identity) :
    first.packet.site.occurrence.identity = last.packet.site.occurrence.identity ∧
    first.packet.declaration.id = last.packet.declaration.id ∧ one.id = two.id
```

```lean
theorem producer_declarations (registry : Registry) (checked : Checked registry)
    (first last : Plan roles)
    (seed : first.packet.context.state.seed = last.packet.context.state.seed)
    (firstVisible : first.packet.declaration ∈ registry.declarations)
    (lastVisible : last.packet.declaration ∈ registry.declarations)
    (one two : Clause) (oneMember : one ∈ first.packet.declaration.requirements)
    (twoMember : two ∈ last.packet.declaration.requirements)
    (oneSignature : one.Signature roles) (twoSignature : two.Signature roles)
    (same : (first.childSite one oneSignature).occurrence.identity =
      (last.childSite two twoSignature).occurrence.identity) :
    first.packet.site.occurrence.identity = last.packet.site.occurrence.identity ∧
    first.packet.declaration = last.packet.declaration ∧ one = two
```

```lean
theorem site_eq_of_centers (first last : Site roles) (same : first.occurrence = last.occurrence)
    (centers : List.ofFn first.center = List.ofFn last.center) : first = last
```

```lean
theorem same_clause_site_equal (first last : Plan roles)
    (seed : first.packet.context.state.seed = last.packet.context.state.seed)
    (invocation : first.packet.site.occurrence.identity = last.packet.site.occurrence.identity)
    (declaration : first.packet.declaration = last.packet.declaration)
    (clause : Clause) (signature : clause.Signature roles)
    (same : (first.childSite clause signature).occurrence = (last.childSite clause signature).occurrence) :
    first.childSite clause signature = last.childSite clause signature
```

```lean
theorem child_site_equal (registry : Registry) (checked : Checked registry)
    (first last : Plan roles)
    (seed : first.packet.context.state.seed = last.packet.context.state.seed)
    (firstVisible : first.packet.declaration ∈ registry.declarations)
    (lastVisible : last.packet.declaration ∈ registry.declarations)
    (one two : Clause) (oneMember : one ∈ first.packet.declaration.requirements)
    (twoMember : two ∈ last.packet.declaration.requirements)
    (oneSignature : one.Signature roles) (twoSignature : two.Signature roles)
    (same : (first.childSite one oneSignature).occurrence =
      (last.childSite two twoSignature).occurrence) :
    first.childSite one oneSignature = last.childSite two twoSignature
```

## GeneralNominalGeneratedSupport184

```lean
theorem roots_append (one : Roots first names) (two : Roots last names) :
    Roots (first.append last) names
```

```lean
theorem schema_roots (query : Query) (origin : Origin) (mode : Mode)
     (known : originSource origin ∈ names) : Roots (schema query origin mode) names
```

```lean
theorem schemas_roots (queries : List Query) (origins : Nat → Origin) (mode : Mode) (offset : Nat)
     (known : ∀ index, originSource (origins index) ∈ names) :
     Roots (schemas queries origins mode offset) names
```

```lean
theorem roots_mono (supported : Roots body first) (included : first ⊆ last) : Roots body last
```

```lean
theorem generated_roots (state : GeneralNominalState.State)
    (interpretation : GeneralNominalInspection.Interpretation) (requests : List Request) :
    Roots (generated state interpretation requests) (requests.map Request.target)
```

```lean
theorem input_request_target (input : InputRequest) (request : Request)
    (member : request ∈ inputRequests input) :
    request.target = input.endpoints.1 ∨ request.target = input.endpoints.2
```

```lean
theorem emitted_target_separate (declaration : Declaration) (clause : Clause)
    (valid : clause.Signature roles) (capture : Capture) (allocation : Allocation roles clause)
    (ins : ∀ name, fresh ≠ (capture.inputs name).1 ∧ fresh ≠ (capture.inputs name).2)
    (outs : ∀ name, fresh ≠ capture.outputs name)
    (args : ∀ index, fresh ≠ (allocation.arguments index).1 ∧ fresh ≠ (allocation.arguments index).2)
    (allocated : ∀ name, fresh ≠ allocation.outputs name)
    (request : Request) (member : request ∈ emissionRequests (emit invocation declaration clause valid capture allocation)) :
    fresh ≠ request.target
```

```lean
theorem root_request_target (declaration : Declaration) (root : GeneralSourceDictionaries.Occurrence roles)
    (request : Request) (member : request ∈ rootRequests declaration root) :
    ∃ output ∈ root.demand.outputs, request.target = output.target
```

```lean
theorem packet_request_separate (packet : GeneralNominalSaturationState.Packet roles)
    (linked : GeneralNominalState.Linked packet.context.state packet.site.occurrence.demand)
    (high : 7 ≤ purpose)
    (outside : fresh packet.context.state.seed invocation declaration purpose owner position ∉
      GeneralNominalState.sources packet.context.state)
    (request : Request)
    (member : request ∈ requests packet.context.state packet.registry packet.site.occurrence
      packet.declaration packet.checked packet.bindings) :
    fresh packet.context.state.seed invocation declaration purpose owner position ≠ request.target
```

```lean
theorem packet_generated_separate (packet : GeneralNominalSaturationState.Packet roles)
    (linked : GeneralNominalState.Linked packet.context.state packet.site.occurrence.demand)
    (high : 7 ≤ purpose)
    (outside : fresh packet.context.state.seed invocation declaration purpose owner position ∉
      GeneralNominalState.sources packet.context.state) :
    fresh packet.context.state.seed invocation declaration purpose owner position ∉
      GeneralNominalRawFrame179.generatedSources (GeneralNominalPacketSupport.capture packet)
        (GeneralNominalRecursiveCandidates.generated packet.registry packet.context packet.site.occurrence
          packet.declaration packet.checked packet.bounds)
```

```lean
theorem packet_linked
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    ∀ packet ∈ state.erased.current.packets,
      GeneralNominalState.Linked packet.context.state packet.site.occurrence.demand
```

```lean
theorem historical_generated_separate
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (packet : GeneralNominalSaturationState.Packet roles) (member : packet ∈ state.erased.current.packets)
    (high : 7 ≤ purpose) :
    fresh context.state.seed invocation declaration purpose owner position ∉
      GeneralNominalRawFrame179.generatedSources (GeneralNominalPacketSupport.capture packet)
        (GeneralNominalRecursiveCandidates.generated packet.registry packet.context packet.site.occurrence
          packet.declaration packet.checked packet.bounds)
```

```lean
theorem ground_generated_separate
    (reachable : B4TargetV5.Reachable (GeneralNominalCenteredGroundBoundary.groundBoundary roles) registry root state)
    (packet : GeneralNominalSaturationState.Packet roles) (member : packet ∈ state.erased.current.packets)
    (high : 7 ≤ purpose) :
    fresh state.erased.current.context.state.seed invocation declaration purpose owner position ∉
      GeneralNominalRawFrame179.generatedSources (GeneralNominalPacketSupport.capture packet)
        (GeneralNominalRecursiveCandidates.generated packet.registry packet.context packet.site.occurrence
          packet.declaration packet.checked packet.bounds)
```

```lean
theorem historical_packet_separate
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (packet : GeneralNominalSaturationState.Packet roles) (member : packet ∈ state.erased.current.packets)
    (high : 7 ≤ purpose) :
    fresh context.state.seed invocation declaration purpose owner position ∉
      GeneralNominalRawFrame179.packetSources packet
```

```lean
theorem ground_packet_separate
    (reachable : B4TargetV5.Reachable (GeneralNominalCenteredGroundBoundary.groundBoundary roles) registry root state)
    (packet : GeneralNominalSaturationState.Packet roles) (member : packet ∈ state.erased.current.packets)
    (high : 7 ≤ purpose) :
    fresh state.erased.current.context.state.seed invocation declaration purpose owner position ∉
      GeneralNominalRawFrame179.packetSources packet
```

## GeneralNominalGroundCandidateReadback184

```lean
theorem registered_inputs
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    ∀ plan ∈ state.plans, plan.input ∈ state.sites
```

```lean
theorem ground_registered_input
    (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (plan : Plan roles) (member : plan ∈ state.plans) : plan.input ∈ state.sites
```

```lean
theorem ground_input_equal (checked : Checked registry)
    (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (historical candidate : Plan roles) (member : historical ∈ state.plans)
    (registered : candidate.input ∈ state.sites)
    (same : candidate.packet.site.occurrence = historical.packet.site.occurrence) :
    candidate.input = historical.input
```

```lean
theorem candidate_actual (checked : Checked registry)
    (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (historical candidate : Plan roles) (member : historical ∈ state.plans)
    (registered : candidate.input ∈ state.sites)
    (same : candidate.packet.site.occurrence = historical.packet.site.occurrence)
    (current : candidate.packet.context = state.erased.current.context)
    (declaration : candidate.packet.declaration = historical.packet.declaration)
    (entry : Use) (present : entry ∈ candidate.headSchema.variables) (actual : entry.mode = .actual)
    (model : Assignment) (valid : Models state model) :
    Same model entry.origin (.source (historical.binder entry.name))
```

```lean
theorem candidate_nonpoint_overlap (checked : Checked registry)
    (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (historical candidate : Plan roles) (member : historical ∈ state.plans)
    (registered : candidate.input ∈ state.sites)
    (same : candidate.packet.site.occurrence = historical.packet.site.occurrence)
    (current : candidate.packet.context = state.erased.current.context)
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

## GeneralNominalGroundHistoricalExtension184

```lean
theorem historical_witnesses
    (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (names : Fin count → Nat) (allocated : BinderNames state names) :
    ∃ historical : Fin count → Origin,
      ∀ index, names index ∈ fullSources state → ActualBinder state (names index) (historical index)
```

```lean
theorem ground_historical_criterion
    (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (arguments : Fin count → NominalArgument)
    (allocated : BinderNames state (fun index => (arguments index).argument.center))
    (previous : Assignment) (valid : Models state previous)
    (linked : ∀ i, (arguments i).argument.endpoints.1 ∈ fullSources state ∧
      (arguments i).argument.endpoints.2 ∈ fullSources state ∧ originSource (arguments i).origin ∈ fullSources state) :
    ∃ historical : Fin count → Origin,
      (∀ index, (arguments index).argument.center ∈ fullSources state →
        ActualBinder state (arguments index).argument.center (historical index)) ∧
      ((∃ extended, Models state extended ∧
        (∀ name ∈ fullSources state, extended name = previous name) ∧ ∀ i, (arguments i).Holds extended) ↔
      (∀ i, ∃ actual, Observes previous (arguments i).origin actual) ∧
      (∀ i actual, Observes previous (arguments i).origin actual →
        GeneralNominalCaptureMerges.Fits previous (arguments i).argument.endpoints actual) ∧
      (∀ i j first last, (arguments i).argument.center = (arguments j).argument.center →
        Observes previous (arguments i).origin first → Observes previous (arguments j).origin last → Equivalent first last) ∧
      (∀ i, (arguments i).argument.center ∈ fullSources state → Same previous (arguments i).origin (historical i)))
```

## GeneralNominalGroundLedgerExtension184

```lean
theorem centered_assign_kept
    (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (names : Fin count → Nat) (values : Fin count → Ty) (high : HighNames state names)
    (model : Assignment) (valid : Models state model)
    (kept : ∀ index, names index ∈ ledgerSources state → values index = (model (names index)).1) :
    Models state (assign model names values)
```

```lean
theorem centered_assign_disjoint
    (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (names : Fin count → Nat) (values : Fin count → Ty) (high : HighNames state names)
    (model : Assignment) (valid : Models state model)
    (outside : ∀ index, names index ∉ ledgerSources state) :
    Models state (assign model names values)
```

```lean
theorem extension_iff_ledger
    (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (arguments : Fin count → NominalArgument)
    (high : HighNames state (fun index => (arguments index).argument.center))
    (previous : Assignment) (valid : Models state previous)
    (linked : ∀ i, (arguments i).argument.endpoints.1 ∈ fullSources state ∧
      (arguments i).argument.endpoints.2 ∈ fullSources state ∧ originSource (arguments i).origin ∈ fullSources state) :
    (∃ extended, Models state extended ∧
      (∀ name ∈ fullSources state, extended name = previous name) ∧ ∀ i, (arguments i).Holds extended) ↔
    (∀ i, ∃ actual, Observes previous (arguments i).origin actual) ∧
    (∀ i actual, Observes previous (arguments i).origin actual →
      GeneralNominalCaptureMerges.Fits previous (arguments i).argument.endpoints actual) ∧
    (∀ i j first last, (arguments i).argument.center = (arguments j).argument.center →
      Observes previous (arguments i).origin first → Observes previous (arguments j).origin last → Equivalent first last) ∧
    (∀ i actual, (arguments i).argument.center ∈ ledgerSources state →
      Observes previous (arguments i).origin actual → Equivalent actual (previous (arguments i).argument.center).1)
```

## GeneralNominalGroundSiteCoherence184

```lean
theorem registered_producers
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    (∀ site ∈ state.sites, root.identity ≤ site.occurrence.identity) ∧
    (∀ plan ∈ state.plans, root.identity ≤ plan.packet.site.occurrence.identity ∧
      plan.packet.declaration ∈ registry.declarations)
```

```lean
theorem emitted_not_root
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (plan : Plan roles) (registered : plan ∈ state.plans)
    (site : Site roles) (emitted : site ∈ plan.emitted) : site.occurrence ≠ root
```

```lean
theorem trace_site_unique (checked : Checked registry)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (first last : Site roles) (one : first ∈ state.sites) (two : last ∈ state.sites)
    (same : first.occurrence = last.occurrence) : first = last
```

```lean
theorem ground_site_unique (checked : Checked registry)
    (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (first last : Site roles) (one : first ∈ state.sites) (two : last ∈ state.sites)
    (same : first.occurrence = last.occurrence) : first = last
```

## GeneralNominalGroundSiteSupport184

```lean
theorem trace_sites_separate
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (high : 7 ≤ purpose) :
    ∀ site ∈ state.erased.current.sites,
      fresh context.state.seed invocation declaration purpose owner position ∉ rawSiteSources site
```

```lean
theorem ground_sites_separate
    (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (site : GeneralNominalDemandMerging.Site roles) (member : site ∈ state.erased.current.sites)
    (high : 7 ≤ purpose) :
    fresh state.erased.current.context.state.seed invocation declaration purpose owner position ∉
      rawSiteSources site
```

## GeneralNominalHeadTransport184

```lean
theorem registered_initial_configuration
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    ∀ plan ∈ state.plans,
      plan.packet.context.state.seed = context.state.seed ∧
      plan.packet.context.state.constructors = context.state.constructors ∧
      plan.packet.context.interpretation = context.interpretation
```

```lean
theorem registered_current_configuration
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (plan : Plan roles) (member : plan ∈ state.plans) :
    plan.packet.context.state.seed = state.erased.current.context.state.seed ∧
    plan.packet.context.state.constructors = state.erased.current.context.state.constructors ∧
    plan.packet.context.interpretation = state.erased.current.context.interpretation
```

```lean
theorem ground_registered_configuration
    (reachable : B4TargetV5.Reachable (GeneralNominalCenteredGroundBoundary.groundBoundary roles) registry root state)
    (plan : Plan roles) (member : plan ∈ state.plans) :
    plan.packet.context.state.seed = state.erased.current.context.state.seed ∧
    plan.packet.context.state.constructors = state.erased.current.context.state.constructors ∧
    plan.packet.context.interpretation = state.erased.current.context.interpretation
```

```lean
theorem head_schema_eq (first last : Plan roles)
    (declaration : first.packet.declaration = last.packet.declaration)
    (constructors : first.packet.context.state.constructors = last.packet.context.state.constructors)
    (interpretation : first.packet.context.interpretation = last.packet.context.interpretation)
    (centers : List.ofFn first.input.center = List.ofFn last.input.center) :
    first.headSchema = last.headSchema
```

```lean
theorem registered_head_schema_eq
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (historical candidate : Plan roles) (member : historical ∈ state.plans)
    (current : candidate.packet.context = state.erased.current.context)
    (declaration : candidate.packet.declaration = historical.packet.declaration)
    (centers : List.ofFn candidate.input.center = List.ofFn historical.input.center) :
    candidate.headSchema = historical.headSchema
```

```lean
theorem ground_head_schema_eq
    (reachable : B4TargetV5.Reachable (GeneralNominalCenteredGroundBoundary.groundBoundary roles) registry root state)
    (historical candidate : Plan roles) (member : historical ∈ state.plans)
    (current : candidate.packet.context = state.erased.current.context)
    (declaration : candidate.packet.declaration = historical.packet.declaration)
    (centers : List.ofFn candidate.input.center = List.ofFn historical.input.center) :
    candidate.headSchema = historical.headSchema
```

```lean
theorem ground_candidate_actual
    (reachable : B4TargetV5.Reachable (GeneralNominalCenteredGroundBoundary.groundBoundary roles) registry root state)
    (historical candidate : Plan roles) (member : historical ∈ state.plans)
    (current : candidate.packet.context = state.erased.current.context)
    (declaration : candidate.packet.declaration = historical.packet.declaration)
    (centers : List.ofFn candidate.input.center = List.ofFn historical.input.center)
    (entry : Use) (present : entry ∈ candidate.headSchema.variables) (actual : entry.mode = .actual)
    (model : Assignment) (valid : Models state model) :
    Same model entry.origin (.source (historical.binder entry.name))
```

```lean
theorem ground_candidate_readback
    (reachable : B4TargetV5.Reachable (GeneralNominalCenteredGroundBoundary.groundBoundary roles) registry root state)
    (historical candidate : Plan roles) (member : historical ∈ state.plans)
    (current : candidate.packet.context = state.erased.current.context)
    (declaration : candidate.packet.declaration = historical.packet.declaration)
    (centers : List.ofFn candidate.input.center = List.ofFn historical.input.center)
    (entry : Use) (present : entry ∈ candidate.headSchema.variables) (actual : entry.mode = .actual)
    (model : Assignment) (valid : Models state model) (value) (seen : Observes model entry.origin value) :
    CommonNominalFullCarrier.Equivalent value (model (historical.binder entry.name)).1
```

```lean
theorem ground_candidate_overlap
    (reachable : B4TargetV5.Reachable (GeneralNominalCenteredGroundBoundary.groundBoundary roles) registry root state)
    (historical candidate : Plan roles) (member : historical ∈ state.plans)
    (current : candidate.packet.context = state.erased.current.context)
    (declaration : candidate.packet.declaration = historical.packet.declaration)
    (centers : List.ofFn candidate.input.center = List.ofFn historical.input.center)
    (entry : Use) (present : entry ∈ candidate.headSchema.variables) (actual : entry.mode = .actual)
    (binder : candidate.binder entry.name = historical.binder entry.name)
    (model : Assignment) (valid : Models state model) :
    Same model entry.origin (.source (candidate.binder entry.name))
```

```lean
theorem nonpoint_binder_eq (first last : Plan roles) (name : Nat)
    (declaration : first.packet.declaration = last.packet.declaration)
    (seed : first.packet.context.state.seed = last.packet.context.state.seed)
    (invocation : first.packet.site.occurrence.identity = last.packet.site.occurrence.identity)
    (input : name ∉ first.packet.declaration.outputNames)
    (firstNonpoint : ((GeneralNominalPacketSupport.capture first.packet).inputs name).1 ≠
      ((GeneralNominalPacketSupport.capture first.packet).inputs name).2)
    (lastNonpoint : ((GeneralNominalPacketSupport.capture last.packet).inputs name).1 ≠
      ((GeneralNominalPacketSupport.capture last.packet).inputs name).2) :
    first.binder name = last.binder name
```

```lean
theorem ground_nonpoint_binder_eq
    (reachable : B4TargetV5.Reachable (GeneralNominalCenteredGroundBoundary.groundBoundary roles) registry root state)
    (historical candidate : Plan roles) (member : historical ∈ state.plans)
    (current : candidate.packet.context = state.erased.current.context)
    (declaration : candidate.packet.declaration = historical.packet.declaration)
    (invocation : candidate.packet.site.occurrence.identity = historical.packet.site.occurrence.identity)
    (name : Nat) (input : name ∉ candidate.packet.declaration.outputNames)
    (candidateNonpoint : ((GeneralNominalPacketSupport.capture candidate.packet).inputs name).1 ≠
      ((GeneralNominalPacketSupport.capture candidate.packet).inputs name).2)
    (historicalNonpoint : ((GeneralNominalPacketSupport.capture historical.packet).inputs name).1 ≠
      ((GeneralNominalPacketSupport.capture historical.packet).inputs name).2) :
    candidate.binder name = historical.binder name
```

```lean
theorem ground_candidate_nonpoint_overlap
    (reachable : B4TargetV5.Reachable (GeneralNominalCenteredGroundBoundary.groundBoundary roles) registry root state)
    (historical candidate : Plan roles) (member : historical ∈ state.plans)
    (current : candidate.packet.context = state.erased.current.context)
    (declaration : candidate.packet.declaration = historical.packet.declaration)
    (invocation : candidate.packet.site.occurrence.identity = historical.packet.site.occurrence.identity)
    (centers : List.ofFn candidate.input.center = List.ofFn historical.input.center)
    (entry : Use) (present : entry ∈ candidate.headSchema.variables) (actual : entry.mode = .actual)
    (input : entry.name ∉ candidate.packet.declaration.outputNames)
    (candidateNonpoint : ((GeneralNominalPacketSupport.capture candidate.packet).inputs entry.name).1 ≠
      ((GeneralNominalPacketSupport.capture candidate.packet).inputs entry.name).2)
    (historicalNonpoint : ((GeneralNominalPacketSupport.capture historical.packet).inputs entry.name).1 ≠
      ((GeneralNominalPacketSupport.capture historical.packet).inputs entry.name).2)
    (model : Assignment) (valid : Models state model) :
    Same model entry.origin (.source (candidate.binder entry.name))
```

## GeneralNominalOverlapIdentity184

```lean
theorem registered_binder_identity
    (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (plan : Plan roles) (registered : plan ∈ state.plans) (name : Nat)
    (equal : plan.binder name =
      fresh state.erased.current.context.state.seed invocation declaration 8 owner position) :
    name = owner ∧ position = 0 ∧
    plan.packet.site.occurrence.identity = invocation ∧ plan.packet.declaration.id = declaration ∧
    name ∉ plan.packet.declaration.outputNames ∧
    ((GeneralNominalPacketSupport.capture plan.packet).inputs name).1 ≠
      ((GeneralNominalPacketSupport.capture plan.packet).inputs name).2
```

```lean
theorem ground_overlap_producer
    (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (member : fresh state.erased.current.context.state.seed invocation declaration 8 owner position ∈
      GeneralNominalModeLedger181.fullSources state) :
    position = 0 ∧ ∃ plan ∈ state.plans, ∃ schema, SchemaLocation plan schema ∧
      ∃ entry ∈ schema.variables, entry.mode = .actual ∧ entry.name = owner ∧
      plan.packet.site.occurrence.identity = invocation ∧ plan.packet.declaration.id = declaration ∧
      owner ∉ plan.packet.declaration.outputNames ∧
      ((GeneralNominalPacketSupport.capture plan.packet).inputs owner).1 ≠
        ((GeneralNominalPacketSupport.capture plan.packet).inputs owner).2 ∧
      plan.binder owner = fresh state.erased.current.context.state.seed invocation declaration 8 owner position
```

```lean
theorem uniform_ground_overlap_producer
    (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (member : fresh state.erased.current.context.state.seed invocation declaration 8 owner position ∈
      GeneralNominalModeLedger181.fullSources state) :
    position = 0 ∧ ∃ plan ∈ state.plans, ∃ schema, SchemaLocation plan schema ∧
      ∃ entry ∈ schema.variables, entry.mode = .actual ∧ entry.name = owner ∧
      plan.packet.site.occurrence.identity = invocation ∧ plan.packet.declaration.id = declaration ∧
      owner ∉ plan.packet.declaration.outputNames ∧
      ((GeneralNominalPacketSupport.capture plan.packet).inputs owner).1 ≠
        ((GeneralNominalPacketSupport.capture plan.packet).inputs owner).2 ∧
      ∀ model, Models state model → GeneralNominalOriginTerms.Same model entry.origin
        (.source (fresh state.erased.current.context.state.seed invocation declaration 8 owner position))
```

## GeneralNominalOverlapProvenance184

```lean
theorem site_endpoint_separate
    (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (site : Site roles) (registered : site ∈ state.sites)
    (index : Fin (roles site.occurrence.demand.role).arity) (high : 7 ≤ purpose) :
    fresh state.erased.current.context.state.seed invocation declaration purpose owner position ≠
      (site.occurrence.demand.arguments index).1 ∧
    fresh state.erased.current.context.state.seed invocation declaration purpose owner position ≠
      (site.occurrence.demand.arguments index).2
```

```lean
theorem site_source_actual
    (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (site : Site roles) (registered : site ∈ state.sites)
    (source : SiteSource site name)
    (allocated : name = fresh state.erased.current.context.state.seed invocation declaration 8 owner position) :
    ∃ origin, ActualBinder state name origin
```

```lean
theorem registered_emitted
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    ∀ plan ∈ state.plans, ∀ site ∈ plan.emitted, site ∈ state.sites
```

```lean
theorem ground_child_registered
    (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (plan : Plan roles) (registered : plan ∈ state.plans)
    (clause : Clause) (member : clause ∈ plan.packet.declaration.requirements)
    (signature : clause.Signature roles) : plan.childSite clause signature ∈ state.sites
```

```lean
theorem head_roots (plan : Plan roles) :
    Roots plan.headSchema (List.ofFn plan.input.center ++ [0])
```

```lean
theorem input_requests_subset (packet : GeneralNominalSaturationState.Packet roles) :
    GeneralNominalPacketSupport.inputRequests packet ⊆
      requests packet.context.state packet.registry packet.site.occurrence packet.declaration packet.checked packet.bindings
```

```lean
theorem ground_request_separate
    (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (plan : Plan roles) (registered : plan ∈ state.plans)
    (request : Request)
    (present : request ∈ requests plan.packet.context.state plan.packet.registry plan.packet.site.occurrence
      plan.packet.declaration plan.packet.checked plan.packet.bindings) (high : 7 ≤ purpose) :
    fresh state.erased.current.context.state.seed invocation declaration purpose owner position ≠ request.target
```

```lean
theorem center_list_actual
    (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (site : Site roles) (registered : site ∈ state.sites)
    (member : name ∈ List.ofFn site.center ++ [0])
    (allocated : name = fresh state.erased.current.context.state.seed invocation declaration 8 owner position) :
    ∃ origin, ActualBinder state name origin
```

```lean
theorem schema_root_actual
    (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (plan : Plan roles) (registered : plan ∈ state.plans)
    (location : GeneralNominalRegisteredReadback182.SchemaLocation plan body)
    (rootMember : (∃ test ∈ body.tests, originSource test.1 = name) ∨
      ∃ entry ∈ body.variables, originSource entry.origin = name)
    (allocated : name = fresh state.erased.current.context.state.seed invocation declaration 8 owner position) :
    ∃ origin, ActualBinder state name origin
```

```lean
theorem ground_registered_packet
    (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (plan : Plan roles) (registered : plan ∈ state.plans) : plan.packet ∈ state.erased.current.packets
```

```lean
theorem schema_source_actual
    (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (plan : Plan roles) (registered : plan ∈ state.plans)
    (location : GeneralNominalRegisteredReadback182.SchemaLocation plan body)
    (source : SchemaSource plan body name)
    (allocated : name = fresh state.erased.current.context.state.seed invocation declaration 8 owner position) :
    ∃ origin, ActualBinder state name origin
```

```lean
theorem plan_source_actual
    (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (plan : Plan roles) (registered : plan ∈ state.plans)
    (source : PlanSource plan name)
    (allocated : name = fresh state.erased.current.context.state.seed invocation declaration 8 owner position) :
    ∃ origin, ActualBinder state name origin
```

```lean
theorem ground_overlap_actual
    (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (member : fresh state.erased.current.context.state.seed invocation declaration 8 owner position ∈
      GeneralNominalModeLedger181.fullSources state) :
    ∃ origin, ActualBinder state
      (fresh state.erased.current.context.state.seed invocation declaration 8 owner position) origin
```

```lean
theorem uniform_ground_overlap_readback
    (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (member : fresh state.erased.current.context.state.seed invocation declaration 8 owner position ∈
      GeneralNominalModeLedger181.fullSources state) :
    ∃ origin, ActualBinder state
      (fresh state.erased.current.context.state.seed invocation declaration 8 owner position) origin ∧
      ∀ model, Models state model → GeneralNominalOriginTerms.Same model origin
        (.source (fresh state.erased.current.context.state.seed invocation declaration 8 owner position))
```

## GeneralNominalRawSeparation184

```lean
theorem ground_raw_separate
    (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (high : 7 ≤ purpose) :
    fresh state.erased.current.context.state.seed invocation declaration purpose owner position ∉
      GeneralNominalRawFrame179.rawSources state.erased.current
```

```lean
theorem raw_assign_preserves
    (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (names : Fin count → Nat) (values : Fin count → CommonNominalFullCarrier.Ty)
    (allocated : ∀ index, ∃ invocation declaration purpose owner position, 7 ≤ purpose ∧
      names index = fresh state.erased.current.context.state.seed invocation declaration purpose owner position)
    (model : Assignment) (valid : GeneralNominalSaturationState.Models state.erased.current model) :
    GeneralNominalSaturationState.Models state.erased.current
      (GeneralNominalCenteredModelExtension.assign model names values)
```

```lean
theorem overlap_iff_ledger
    (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (high : 7 ≤ purpose) :
    fresh state.erased.current.context.state.seed invocation declaration purpose owner position ∈
      GeneralNominalModeLedger181.fullSources state ↔
    fresh state.erased.current.context.state.seed invocation declaration purpose owner position ∈
      GeneralNominalModeLedger181.ledgerSources state
```

## GeneralNominalRootExtension184

```lean
theorem root_extension_iff (checked : Checked registry)
    (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (candidate : Plan roles) (registered : candidate.input ∈ state.sites)
    (atRoot : candidate.packet.site.occurrence = root)
    (current : candidate.packet.context = state.erased.current.context)
    (visible : candidate.packet.declaration ∈ registry.declarations)
    (entries : Fin count → Use)
    (present : ∀ i, entries i ∈ candidate.headSchema.variables)
    (actual : ∀ i, (entries i).mode = .actual)
    (input : ∀ i, (entries i).name ∉ candidate.packet.declaration.outputNames)
    (nonpoint : ∀ i, ((GeneralNominalPacketSupport.capture candidate.packet).inputs (entries i).name).1 ≠
      ((GeneralNominalPacketSupport.capture candidate.packet).inputs (entries i).name).2)
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

## GeneralNominalRootOverlap184

```lean
theorem trace_root_identity
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (site : Site roles) (registered : site ∈ state.sites)
    (identity : site.occurrence.identity = root.identity) : site.occurrence = root
```

```lean
theorem ground_plan_root_identity
    (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (plan : Plan roles) (member : plan ∈ state.plans)
    (identity : plan.packet.site.occurrence.identity = root.identity) :
    plan.packet.site.occurrence = root
```

```lean
theorem ground_plan_visible
    (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (plan : Plan roles) (member : plan ∈ state.plans) :
    plan.packet.declaration ∈ registry.declarations
```

```lean
theorem candidate_root_overlap (checked : Checked registry)
    (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (candidate : Plan roles) (registered : candidate.input ∈ state.sites)
    (atRoot : candidate.packet.site.occurrence = root)
    (current : candidate.packet.context = state.erased.current.context)
    (visible : candidate.packet.declaration ∈ registry.declarations)
    (entry : Use) (present : entry ∈ candidate.headSchema.variables) (actual : entry.mode = .actual)
    (input : entry.name ∉ candidate.packet.declaration.outputNames)
    (nonpoint : ((GeneralNominalPacketSupport.capture candidate.packet).inputs entry.name).1 ≠
      ((GeneralNominalPacketSupport.capture candidate.packet).inputs entry.name).2)
    (overlap : candidate.binder entry.name ∈ GeneralNominalModeLedger181.fullSources state)
    (model : Assignment) (valid : Models state model) :
    Same model entry.origin (.source (candidate.binder entry.name))
```

## GeneralNominalSiteSeparation184

```lean
theorem clause_endpoints (packet : GeneralNominalSaturationState.Packet roles)
    (clause : Clause) (signature : clause.Signature roles)
    (high : 7 ≤ purpose)
    (outside : fresh packet.context.state.seed invocation declaration purpose owner position ∉
      GeneralNominalState.sources packet.context.state)
    (index : Fin (roles clause.role).arity) :
    fresh packet.context.state.seed invocation declaration purpose owner position ≠
      ((GeneralNominalFeedbackSites.clauseChild packet clause signature).demand.arguments index).1 ∧
    fresh packet.context.state.seed invocation declaration purpose owner position ≠
      ((GeneralNominalFeedbackSites.clauseChild packet clause signature).demand.arguments index).2
```

```lean
theorem child_endpoints (packet : GeneralNominalSaturationState.Packet roles)
    (child : Occurrence roles) (member : child ∈ packet.children)
    (high : 7 ≤ purpose)
    (outside : fresh packet.context.state.seed invocation declaration purpose owner position ∉
      GeneralNominalState.sources packet.context.state) :
    ∀ index, fresh packet.context.state.seed invocation declaration purpose owner position ≠
      (child.demand.arguments index).1 ∧
      fresh packet.context.state.seed invocation declaration purpose owner position ≠
      (child.demand.arguments index).2
```

```lean
theorem child_separate (packet : GeneralNominalSaturationState.Packet roles)
    (child : Occurrence roles) (member : child ∈ packet.children)
    (high : 7 ≤ purpose)
    (context : fresh packet.context.state.seed invocation declaration purpose owner position ∉
      GeneralNominalState.sources packet.context.state)
    (parent : fresh packet.context.state.seed invocation declaration purpose owner position ∉
      rawSiteSources packet.site) :
    fresh packet.context.state.seed invocation declaration purpose owner position ∉
      rawSiteSources (GeneralNominalSharedEmission.childSite packet child)
```

## GeneralNominalSiteSupport184

```lean
theorem sources_iff (site : Site roles) (names : List Nat) :
    rawSiteSources site ⊆ names ↔ Endpoints site names ∧ Origins site names
```

```lean
theorem point_origins (occurrence : Occurrence roles)
    (endpoints : ∀ index, (occurrence.demand.arguments index).1 ∈ names) :
    Origins (pointSite occurrence) names
```

```lean
theorem point_sources (occurrence : Occurrence roles)
    (endpoints : ∀ index, (occurrence.demand.arguments index).1 ∈ names ∧
      (occurrence.demand.arguments index).2 ∈ names) :
    rawSiteSources (pointSite occurrence) ⊆ names
```

```lean
theorem recover_origins (state : GeneralNominalSaturationState.State roles) (site : Site roles)
    (old : Origins site names) (endpoints : ∀ index, (site.occurrence.demand.arguments index).1 ∈ names) :
    Origins (GeneralNominalFeedbackSites.recover state site) names
```

```lean
theorem recover_sources (state : GeneralNominalSaturationState.State roles) (site : Site roles)
    (support : rawSiteSources site ⊆ names) :
    rawSiteSources (GeneralNominalFeedbackSites.recover state site) ⊆ names
```

```lean
theorem inherited_roots (packet : GeneralNominalSaturationState.Packet roles) :
    GeneralNominalRawOrigin182.ReportRoots
      (GeneralNominalSharedCaptures.inheritedReport packet) (inheritedSources packet)
```

```lean
theorem usable_root (packet : GeneralNominalSaturationState.Packet roles)
    (usable : GeneralNominalSharedCaptures.Usable packet name origin) :
    originSource origin ∈ inheritedSources packet
```

```lean
theorem feedback_root (packet : GeneralNominalSaturationState.Packet roles)
    (recorded : GeneralNominalFeedbackSites.OriginAt packet child position origin) :
    originSource origin ∈ GeneralNominalState.sources packet.context.state
```

```lean
theorem child_origin_sources (packet : GeneralNominalSaturationState.Packet roles)
    (child : Occurrence roles) (index : Fin (roles child.demand.role).arity)
    (origin : Origin) (recorded : GeneralNominalSharedEmission.childOrigin packet child index = some origin) :
    originSource origin ∈ inheritedSources packet ∨
      originSource origin = (child.demand.arguments index).1
```

```lean
theorem child_sources (packet : GeneralNominalSaturationState.Packet roles)
    (child : Occurrence roles) (old : inheritedSources packet ⊆ names)
    (endpoints : ∀ index, (child.demand.arguments index).1 ∈ names ∧
      (child.demand.arguments index).2 ∈ names) :
    rawSiteSources (GeneralNominalSharedEmission.childSite packet child) ⊆ names
```
