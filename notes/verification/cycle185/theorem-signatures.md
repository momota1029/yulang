```lean
theorem registered_binder_identity
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (plan : Plan roles) (registered : plan ∈ state.core.plans) (name : Nat)
    (equal : plan.binder name =
      fresh state.core.erased.current.context.state.seed invocation declaration 8 owner position) :
    name = owner ∧ position = 0 ∧
    plan.packet.site.occurrence.identity = invocation ∧ plan.packet.declaration.id = declaration ∧
    name ∉ plan.packet.declaration.outputNames ∧
    ((GeneralNominalPacketSupport.capture plan.packet).inputs name).1 ≠
      ((GeneralNominalPacketSupport.capture plan.packet).inputs name).2
```

```lean
theorem registered_inputs
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    ∀ plan ∈ state.core.plans, plan.input ∈ state.core.sites
```

```lean
theorem wf_registered_input
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (plan : Plan roles) (member : plan ∈ state.core.plans) : plan.input ∈ state.core.sites
```

```lean
theorem wf_input_equal (checked : Checked registry)
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (historical candidate : Plan roles) (member : historical ∈ state.core.plans)
    (registered : candidate.input ∈ state.core.sites)
    (same : candidate.packet.site.occurrence = historical.packet.site.occurrence) :
    candidate.input = historical.input
```

```lean
theorem candidate_actual (checked : Checked registry)
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (historical candidate : Plan roles) (member : historical ∈ state.core.plans)
    (registered : candidate.input ∈ state.core.sites)
    (same : candidate.packet.site.occurrence = historical.packet.site.occurrence)
    (current : candidate.packet.context = state.core.erased.current.context)
    (declaration : candidate.packet.declaration = historical.packet.declaration)
    (entry : Use) (present : entry ∈ candidate.headSchema.variables) (actual : entry.mode = .actual)
    (model : Assignment) (valid : Models state model) :
    Same model entry.origin (.source (historical.binder entry.name))
```

```lean
theorem candidate_nonpoint_overlap (checked : Checked registry)
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (historical candidate : Plan roles) (member : historical ∈ state.core.plans)
    (registered : candidate.input ∈ state.core.sites)
    (same : candidate.packet.site.occurrence = historical.packet.site.occurrence)
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

```lean
theorem registered_finished
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    ∀ plan ∈ state.core.plans, Finished (headInspection plan)
```

```lean
theorem site_needed (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (site : Site roles) (member : site ∈ state.core.sites)
    (index : Fin (roles site.occurrence.demand.role).arity)
    (center : site.center index = fresh state.core.erased.current.context.state.seed invocation declaration 8 owner position) :
    ∃ plan ∈ state.core.plans, ∃ name, GeneralNominalSharedCaptures.Needed plan.packet name ∧ plan.binder name = site.center index
```

```lean
theorem registered_input_actual
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (plan : Plan roles) (registered : plan ∈ state.core.plans) (name : Nat)
    (named : name ∈ plan.packet.declaration.inputNames) :
    ∃ origin, ActualBinder state.core (plan.binder name) origin
```

```lean
theorem registered_capture_actual
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (plan : Plan roles) (registered : plan ∈ state.core.plans) (name : Nat)
    (needed : name ∈ plan.packet.declaration.inputNames ∨ GeneralNominalSharedCaptures.Needed plan.packet name) :
    ∃ origin, ActualBinder state.core (plan.binder name) origin
```

```lean
theorem wf_capture_actual
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (plan : Plan roles) (registered : plan ∈ state.core.plans) (name : Nat)
    (needed : name ∈ plan.packet.declaration.inputNames ∨ GeneralNominalSharedCaptures.Needed plan.packet name) :
    ∃ origin, ActualBinder state.core (plan.binder name) origin
```

```lean
theorem uniform_wf_capture_readback
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (plan : Plan roles) (registered : plan ∈ state.core.plans) (name : Nat)
    (needed : name ∈ plan.packet.declaration.inputNames ∨ GeneralNominalSharedCaptures.Needed plan.packet name) :
    ∃ origin, ActualBinder state.core (plan.binder name) origin ∧
      ∀ model, Models state model → GeneralNominalOriginTerms.Same model origin (.source (plan.binder name))
```

```lean
theorem uniform_wf_site_readback
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (site : Site roles) (member : site ∈ state.core.sites)
    (index : Fin (roles site.occurrence.demand.role).arity)
    (center : site.center index = fresh state.core.erased.current.context.state.seed
      invocation declaration 8 owner position) :
    ∃ origin, ActualBinder state.core (site.center index) origin ∧
      ∀ model, Models state model → GeneralNominalOriginTerms.Same model origin (.source (site.center index))
```

```lean
theorem registered_packets
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    ∀ plan ∈ state.core.plans, plan.packet ∈ state.core.erased.current.packets
```

```lean
theorem capture_separate
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (packet : GeneralNominalSaturationState.Packet roles) (member : packet ∈ state.core.erased.current.packets)
    (high : 7 ≤ purpose) (name : Nat) :
    fresh state.core.erased.current.context.state.seed invocation declaration purpose owner position ≠
      (GeneralNominalPacketSupport.capture packet).outputs name ∧
    fresh state.core.erased.current.context.state.seed invocation declaration purpose owner position ≠
      ((GeneralNominalPacketSupport.capture packet).inputs name).1 ∧
    fresh state.core.erased.current.context.state.seed invocation declaration purpose owner position ≠
      ((GeneralNominalPacketSupport.capture packet).inputs name).2
```

```lean
theorem site_endpoint_separate
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (site : Site roles) (registered : site ∈ state.core.sites)
    (index : Fin (roles site.occurrence.demand.role).arity) (high : 7 ≤ purpose) :
    fresh state.core.erased.current.context.state.seed invocation declaration purpose owner position ≠
      (site.occurrence.demand.arguments index).1 ∧
    fresh state.core.erased.current.context.state.seed invocation declaration purpose owner position ≠
      (site.occurrence.demand.arguments index).2
```

```lean
theorem site_source_actual
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (site : Site roles) (registered : site ∈ state.core.sites)
    (source : SiteSource site name)
    (allocated : name = fresh state.core.erased.current.context.state.seed invocation declaration 8 owner position) :
    ∃ origin, ActualBinder state.core name origin
```

```lean
theorem registered_emitted
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    ∀ plan ∈ state.core.plans, ∀ site ∈ plan.emitted, site ∈ state.core.sites
```

```lean
theorem wf_child_registered
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (plan : Plan roles) (registered : plan ∈ state.core.plans)
    (clause : Clause) (member : clause ∈ plan.packet.declaration.requirements)
    (signature : clause.Signature roles) : plan.childSite clause signature ∈ state.core.sites
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
theorem wf_request_separate
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (plan : Plan roles) (registered : plan ∈ state.core.plans)
    (request : Request)
    (present : request ∈ requests plan.packet.context.state plan.packet.registry plan.packet.site.occurrence
      plan.packet.declaration plan.packet.checked plan.packet.bindings) (high : 7 ≤ purpose) :
    fresh state.core.erased.current.context.state.seed invocation declaration purpose owner position ≠ request.target
```

```lean
theorem center_list_actual
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (site : Site roles) (registered : site ∈ state.core.sites)
    (member : name ∈ List.ofFn site.center ++ [0])
    (allocated : name = fresh state.core.erased.current.context.state.seed invocation declaration 8 owner position) :
    ∃ origin, ActualBinder state.core name origin
```

```lean
theorem schema_root_actual
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (plan : Plan roles) (registered : plan ∈ state.core.plans)
    (location : GeneralNominalRegisteredReadback182.SchemaLocation plan body)
    (rootMember : (∃ test ∈ body.tests, originSource test.1 = name) ∨
      ∃ entry ∈ body.variables, originSource entry.origin = name)
    (allocated : name = fresh state.core.erased.current.context.state.seed invocation declaration 8 owner position) :
    ∃ origin, ActualBinder state.core name origin
```

```lean
theorem wf_registered_packet
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (plan : Plan roles) (registered : plan ∈ state.core.plans) : plan.packet ∈ state.core.erased.current.packets
```

```lean
theorem schema_source_actual
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (plan : Plan roles) (registered : plan ∈ state.core.plans)
    (location : GeneralNominalRegisteredReadback182.SchemaLocation plan body)
    (source : SchemaSource plan body name)
    (allocated : name = fresh state.core.erased.current.context.state.seed invocation declaration 8 owner position) :
    ∃ origin, ActualBinder state.core name origin
```

```lean
theorem plan_source_actual
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (plan : Plan roles) (registered : plan ∈ state.core.plans)
    (source : PlanSource plan name)
    (allocated : name = fresh state.core.erased.current.context.state.seed invocation declaration 8 owner position) :
    ∃ origin, ActualBinder state.core name origin
```

```lean
theorem wf_overlap_actual
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (member : fresh state.core.erased.current.context.state.seed invocation declaration 8 owner position ∈
      GeneralNominalModeLedger181.fullSources state.core) :
    ∃ origin, ActualBinder state.core
      (fresh state.core.erased.current.context.state.seed invocation declaration 8 owner position) origin
```

```lean
theorem uniform_wf_overlap_readback
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (member : fresh state.core.erased.current.context.state.seed invocation declaration 8 owner position ∈
      GeneralNominalModeLedger181.fullSources state.core) :
    ∃ origin, ActualBinder state.core
      (fresh state.core.erased.current.context.state.seed invocation declaration 8 owner position) origin ∧
      ∀ model, Models state model → GeneralNominalOriginTerms.Same model origin
        (.source (fresh state.core.erased.current.context.state.seed invocation declaration 8 owner position))
```

```lean
theorem head_sources_subset (plan : Plan roles) :
    headSources plan ⊆ GeneralNominalModeLedger181.equationSources plan
```

```lean
theorem effect_plan_registered
    (reachable : B4TargetV6.Reachable (GeneralNominalCenteredHeadWFBoundary.boundary roles) registry root state)
    (effect : Effect roles) (member : effect ∈ state.effects) : effect.plan ∈ state.core.plans
```

```lean
theorem effect_head_in_core
    (reachable : B4TargetV6.Reachable (GeneralNominalCenteredHeadWFBoundary.boundary roles) registry root state)
    (effect : Effect roles) (member : effect ∈ state.effects) :
    headSources effect.plan ⊆ GeneralNominalModeLedger181.fullSources state.core
```

```lean
theorem wf_request_separate
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (focus : Occurrence roles) (output : GeneralSourceState.Output)
    (member : output ∈ requests state.core focus) (high : 7 ≤ purpose) :
    fresh state.core.erased.current.context.state.seed invocation declaration purpose owner position ≠ output.target
```

```lean
theorem wf_effect_packet_seed
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (effect : Effect roles) (member : effect ∈ state.effects) :
    effect.plan.packet.context.state.seed = state.core.erased.current.context.state.seed
```

```lean
theorem wf_effect_context_separate
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (effect : Effect roles) (member : effect ∈ state.effects) (high : 7 ≤ purpose) :
    fresh effect.plan.packet.context.state.seed invocation declaration purpose owner position ∉
      GeneralNominalState.sources effect.plan.packet.context.state
```

```lean
theorem wf_live_overlap_iff
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (effect : Effect roles) (member : effect ∈ state.effects) (high : 7 ≤ purpose) :
    fresh state.core.erased.current.context.state.seed invocation declaration purpose owner position ∈
      GeneralNominalHeadLedgerFrame182.outputSources state.core effect.plan.packet.site.occurrence effect.plan ↔
    ∃ entry ∈ (outputSchema state.core effect.plan.packet.site.occurrence effect.plan).variables,
      entry.mode = .actual ∧
      fresh state.core.erased.current.context.state.seed invocation declaration purpose owner position = effect.plan.binder entry.name
```

```lean
theorem wf_live_overlap_readback
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (effect : Effect roles) (member : effect ∈ state.effects) (high : 7 ≤ purpose)
    (overlap : fresh state.core.erased.current.context.state.seed invocation declaration purpose owner position ∈
      GeneralNominalHeadLedgerFrame182.outputSources state.core effect.plan.packet.site.occurrence effect.plan) :
    ∃ entry ∈ (outputSchema state.core effect.plan.packet.site.occurrence effect.plan).variables,
      entry.mode = .actual ∧
      fresh state.core.erased.current.context.state.seed invocation declaration purpose owner position = effect.plan.binder entry.name ∧
      ∀ model : Assignment, Models state model →
        GeneralNominalOriginTerms.Same model entry.origin
          (.source (fresh state.core.erased.current.context.state.seed invocation declaration purpose owner position))
```

```lean
theorem wf_snapshot_overlap_iff
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (effect : Effect roles) (member : effect ∈ state.effects) (high : 7 ≤ purpose) :
    fresh state.core.erased.current.context.state.seed invocation declaration purpose owner position ∈
      GeneralNominalHeadLedgerFrame182.outputSources effect.snapshot effect.plan.packet.site.occurrence effect.plan ↔
    ∃ entry ∈ (outputSchema effect.snapshot effect.plan.packet.site.occurrence effect.plan).variables,
      entry.mode = .actual ∧
      fresh state.core.erased.current.context.state.seed invocation declaration purpose owner position = effect.plan.binder entry.name
```

```lean
theorem wf_snapshot_overlap_readback
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (effect : Effect roles) (member : effect ∈ state.effects) (high : 7 ≤ purpose)
    (overlap : fresh state.core.erased.current.context.state.seed invocation declaration purpose owner position ∈
      GeneralNominalHeadLedgerFrame182.outputSources effect.snapshot effect.plan.packet.site.occurrence effect.plan) :
    ∃ entry ∈ (outputSchema effect.snapshot effect.plan.packet.site.occurrence effect.plan).variables,
      entry.mode = .actual ∧
      fresh state.core.erased.current.context.state.seed invocation declaration purpose owner position = effect.plan.binder entry.name ∧
      ∀ model : Assignment, Models state model →
        GeneralNominalOriginTerms.Same model entry.origin
          (.source (fresh state.core.erased.current.context.state.seed invocation declaration purpose owner position))
```

```lean
theorem trace_plans_effects
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    state.core.plans = state.effects.map Effect.plan
```

```lean
theorem trace_effect_origin
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    ∀ effect ∈ state.effects, ∃ before,
      B4Target.Steps (Step registry root) (initial context root) before ∧
      effect.snapshot = before.core ∧
      effect.plan.packet.context = before.core.erased.current.context ∧
      effect.registry = registry
```

```lean
theorem trace_effect_configuration
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (effect : Effect roles) (member : effect ∈ state.effects) :
    effect.snapshot.erased.current.context.state.seed = context.state.seed ∧
    effect.snapshot.erased.current.context.state.constructors = context.state.constructors ∧
    effect.snapshot.erased.current.context.interpretation = context.interpretation
```

```lean
theorem trace_effect_plan_configuration
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (effect : Effect roles) (member : effect ∈ state.effects) :
    effect.plan.packet.context.state.seed = context.state.seed ∧
    effect.plan.packet.context.state.constructors = context.state.constructors ∧
    effect.plan.packet.context.interpretation = context.interpretation
```

```lean
theorem trace_registered_plan_iff
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (plan : Plan roles) :
    plan ∈ state.core.plans ↔ ∃ effect ∈ state.effects, effect.plan = plan
```

```lean
theorem wf_plans_effects
    (reachable : B4TargetV6.Reachable (GeneralNominalCenteredHeadWFBoundary.boundary roles) registry root state) :
    state.core.plans = state.effects.map Effect.plan
```

```lean
theorem wf_effect_snapshot_reachable
    (reachable : B4TargetV6.Reachable (GeneralNominalCenteredHeadWFBoundary.boundary roles) registry root state)
    (effect : Effect roles) (member : effect ∈ state.effects) :
    ∃ before, B4TargetV6.Reachable (GeneralNominalCenteredHeadWFBoundary.boundary roles) registry root before ∧
      effect.snapshot = before.core ∧ effect.registry = registry
```

```lean
theorem wf_effect_seed
    (reachable : B4TargetV6.Reachable (GeneralNominalCenteredHeadWFBoundary.boundary roles) registry root state)
    (effect : Effect roles) (member : effect ∈ state.effects) :
    effect.snapshot.erased.current.context.state.seed = state.core.erased.current.context.state.seed
```

```lean
theorem wf_full_overlap_readback
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (member : fresh state.core.erased.current.context.state.seed invocation declaration 8 owner position ∈ fullSources state) :
    ∃ origin : Origin, ∀ model : Assignment, Models state model →
      Same model origin (.source (fresh state.core.erased.current.context.state.seed invocation declaration 8 owner position))
```

```lean
theorem wf_historical_witnesses
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (names : Fin count → Nat) (allocated : BinderNames state names) :
    ∃ historical : Fin count → Origin, ∀ index, names index ∈ fullSources state →
      ∀ model : Assignment, Models state model → Same model (historical index) (.source (names index))
```

```lean
theorem wf_full_producer
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (member : fresh state.core.erased.current.context.state.seed invocation declaration 8 owner position ∈ fullSources state) :
    ∃ plan ∈ state.core.plans, ∃ name,
      plan.binder name = fresh state.core.erased.current.context.state.seed invocation declaration 8 owner position
```

```lean
theorem historical_agreement_iff (recorded : Same model historical (.source name)) :
    ((∃ value, Observes model candidate value) ∧
      ∀ value, Observes model candidate value → Equivalent value (model name).1) ↔
    Same model candidate historical
```

```lean
theorem wf_extension_iff_historical
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (arguments : Fin count → NominalArgument)
    (allocated : BinderNames state (fun index => (arguments index).argument.center))
    (previous : Assignment) (valid : Models state previous)
    (linked : ∀ i, (arguments i).argument.endpoints.1 ∈ fullSources state ∧
      (arguments i).argument.endpoints.2 ∈ fullSources state ∧ originSource (arguments i).origin ∈ fullSources state) :
    ∃ historical : Fin count → Origin,
      (∀ i, (arguments i).argument.center ∈ fullSources state →
        ∀ model, Models state model → Same model (historical i) (.source (arguments i).argument.center)) ∧
      ((∃ extended, Models state extended ∧
        (∀ name ∈ fullSources state, extended name = previous name) ∧ ∀ i, (arguments i).Holds extended) ↔
      (∀ i, ∃ actual, Observes previous (arguments i).origin actual) ∧
      (∀ i actual, Observes previous (arguments i).origin actual →
        GeneralNominalCaptureMerges.Fits previous (arguments i).argument.endpoints actual) ∧
      (∀ i j first last, (arguments i).argument.center = (arguments j).argument.center →
        Observes previous (arguments i).origin first → Observes previous (arguments j).origin last → Equivalent first last) ∧
      (∀ i, (arguments i).argument.center ∈ fullSources state → Same previous (arguments i).origin (historical i)))
```

```lean
theorem output_roots (state : GeneralNominalCenteredSteps.State roles)
    (root : Occurrence roles) (plan : Plan roles) :
    Roots (outputSchema state root plan) ((requests state root).map (·.target))
```

```lean
theorem output_overlap_iff (state : GeneralNominalCenteredSteps.State roles)
    (root : Occurrence roles) (plan : Plan roles) (high : 7 ≤ purpose)
    (outside : fresh plan.packet.context.state.seed invocation declaration purpose owner position ∉
      GeneralNominalState.sources plan.packet.context.state)
    (targets : ∀ output ∈ requests state root,
      fresh plan.packet.context.state.seed invocation declaration purpose owner position ≠ output.target) :
    fresh plan.packet.context.state.seed invocation declaration purpose owner position ∈ outputSources state root plan ↔
    ∃ entry ∈ (outputSchema state root plan).variables, entry.mode = .actual ∧
      fresh plan.packet.context.state.seed invocation declaration purpose owner position = plan.binder entry.name
```

```lean
theorem output_overlap_readback (state : GeneralNominalCenteredSteps.State roles)
    (root : Occurrence roles) (plan : Plan roles) (high : 7 ≤ purpose)
    (outside : fresh plan.packet.context.state.seed invocation declaration purpose owner position ∉
      GeneralNominalState.sources plan.packet.context.state)
    (targets : ∀ output ∈ requests state root,
      fresh plan.packet.context.state.seed invocation declaration purpose owner position ≠ output.target)
    (overlap : fresh plan.packet.context.state.seed invocation declaration purpose owner position ∈ outputSources state root plan) :
    ∃ entry ∈ (outputSchema state root plan).variables, entry.mode = .actual ∧
      fresh plan.packet.context.state.seed invocation declaration purpose owner position = plan.binder entry.name ∧
      ∀ model : Assignment, OutputEquations state root plan model →
        GeneralNominalOriginTerms.Same model entry.origin
          (.source (fresh plan.packet.context.state.seed invocation declaration purpose owner position))
```

```lean
theorem packet_context_pool
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    ∀ packet ∈ state.core.erased.current.packets,
      GeneralNominalState.sources packet.context.state ⊆ pool registry context root limit
```

```lean
theorem packet_report_pool
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (packet : GeneralNominalSaturationState.Packet roles) (member : packet ∈ state.core.erased.current.packets) :
    GeneralNominalRawFrame179.reportSources packet.context.state
      (GeneralNominalRecursiveCandidates.report packet.context packet.declaration packet.bounds) ⊆
      pool registry context root limit
```

```lean
theorem fresh_outside_packet_report
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (packet : GeneralNominalSaturationState.Packet roles) (member : packet ∈ state.core.erased.current.packets)
    (centerPurpose : 7 ≤ purpose) :
    GeneralNominalCenters.fresh context.state.seed invocation declaration purpose owner position ∉
      GeneralNominalRawFrame179.reportSources packet.context.state
        (GeneralNominalRecursiveCandidates.report packet.context packet.declaration packet.bounds)
```

```lean
theorem packet_private_pool
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    ∀ packet ∈ state.core.erased.current.packets,
      GeneralNominalState.sources packet.privateContext.state ⊆ pool registry context root limit
```

```lean
theorem packet_seed
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    ∀ packet ∈ state.core.erased.current.packets, packet.context.state.seed = context.state.seed
```

```lean
theorem historical_private_separate
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (packet : GeneralNominalSaturationState.Packet roles) (member : packet ∈ state.core.erased.current.packets)
    (high : 7 ≤ purpose) :
    fresh context.state.seed invocation declaration purpose owner position ∉
      GeneralNominalState.sources packet.privateContext.state
```

```lean
theorem packet_outputs_pool
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    ∀ packet ∈ state.core.erased.current.packets, ∀ output ∈ packet.site.occurrence.demand.outputs,
      output.target ∈ pool registry context root limit
```

```lean
theorem packet_request_separate (packet : GeneralNominalSaturationState.Packet roles)
    (high : 7 ≤ purpose)
    (outputs : ∀ output ∈ packet.site.occurrence.demand.outputs,
      fresh packet.context.state.seed invocation declaration purpose owner position ≠ output.target)
    (outside : fresh packet.context.state.seed invocation declaration purpose owner position ∉
      GeneralNominalState.sources packet.context.state)
    (request : Request)
    (member : request ∈ requests packet.context.state packet.registry packet.site.occurrence
      packet.declaration packet.checked packet.bindings) :
    fresh packet.context.state.seed invocation declaration purpose owner position ≠ request.target
```

```lean
theorem packet_generated_separate (packet : GeneralNominalSaturationState.Packet roles)
    (high : 7 ≤ purpose)
    (outputs : ∀ output ∈ packet.site.occurrence.demand.outputs,
      fresh packet.context.state.seed invocation declaration purpose owner position ≠ output.target)
    (outside : fresh packet.context.state.seed invocation declaration purpose owner position ∉
      GeneralNominalState.sources packet.context.state) :
    fresh packet.context.state.seed invocation declaration purpose owner position ∉
      GeneralNominalRawFrame179.generatedSources (GeneralNominalPacketSupport.capture packet)
        (GeneralNominalRecursiveCandidates.generated packet.registry packet.context packet.site.occurrence
          packet.declaration packet.checked packet.bounds)
```

```lean
theorem historical_generated_separate
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (packet : GeneralNominalSaturationState.Packet roles) (member : packet ∈ state.core.erased.current.packets)
    (high : 7 ≤ purpose) :
    fresh context.state.seed invocation declaration purpose owner position ∉
      GeneralNominalRawFrame179.generatedSources (GeneralNominalPacketSupport.capture packet)
        (GeneralNominalRecursiveCandidates.generated packet.registry packet.context packet.site.occurrence
          packet.declaration packet.checked packet.bounds)
```

```lean
theorem historical_packet_separate
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (packet : GeneralNominalSaturationState.Packet roles) (member : packet ∈ state.core.erased.current.packets)
    (high : 7 ≤ purpose) :
    fresh context.state.seed invocation declaration purpose owner position ∉
      GeneralNominalRawFrame179.packetSources packet
```

```lean
theorem trace_raw_separate
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (high : 7 ≤ purpose) :
    fresh context.state.seed invocation declaration purpose owner position ∉
      GeneralNominalRawFrame179.rawSources state.core.erased.current
```

```lean
theorem wf_raw_separate
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (high : 7 ≤ purpose) :
    fresh state.core.erased.current.context.state.seed invocation declaration purpose owner position ∉
      GeneralNominalRawFrame179.rawSources state.core.erased.current
```

```lean
theorem wf_overlap_iff_residual
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (high : 7 ≤ purpose) :
    fresh state.core.erased.current.context.state.seed invocation declaration purpose owner position ∈
      GeneralNominalHeadLedgerFrame182.fullSources state ↔
    fresh state.core.erased.current.context.state.seed invocation declaration purpose owner position ∈
      residualSources state
```

```lean
theorem wf_raw_assign
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (names : Fin count → Nat) (values : Fin count → CommonNominalFullCarrier.Ty)
    (allocated : Allocated state names) (model : Assignment)
    (valid : GeneralNominalSaturationState.Models state.core.erased.current model) :
    GeneralNominalSaturationState.Models state.core.erased.current
      (GeneralNominalCenteredModelExtension.assign model names values)
```

```lean
theorem wf_models_assign
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (names : Fin count → Nat) (values : Fin count → CommonNominalFullCarrier.Ty)
    (allocated : Allocated state names) (model : Assignment) (valid : Models state model)
    (kept : ∀ index, names index ∈ residualSources state → values index = (model (names index)).1) :
    Models state (GeneralNominalCenteredModelExtension.assign model names values)
```

```lean
theorem registered_initial_configuration
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    ∀ plan ∈ state.core.plans,
      plan.packet.context.state.seed = context.state.seed ∧
      plan.packet.context.state.constructors = context.state.constructors ∧
      plan.packet.context.interpretation = context.interpretation
```

```lean
theorem registered_current_configuration
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (plan : Plan roles) (member : plan ∈ state.core.plans) :
    plan.packet.context.state.seed = state.core.erased.current.context.state.seed ∧
    plan.packet.context.state.constructors = state.core.erased.current.context.state.constructors ∧
    plan.packet.context.interpretation = state.core.erased.current.context.interpretation
```

```lean
theorem wf_registered_configuration
    (reachable : B4TargetV6.Reachable (GeneralNominalCenteredHeadWFBoundary.boundary roles) registry root state)
    (plan : Plan roles) (member : plan ∈ state.core.plans) :
    plan.packet.context.state.seed = state.core.erased.current.context.state.seed ∧
    plan.packet.context.state.constructors = state.core.erased.current.context.state.constructors ∧
    plan.packet.context.interpretation = state.core.erased.current.context.interpretation
```

```lean
theorem registered_head_schema_eq
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (historical candidate : Plan roles) (member : historical ∈ state.core.plans)
    (current : candidate.packet.context = state.core.erased.current.context)
    (declaration : candidate.packet.declaration = historical.packet.declaration)
    (centers : List.ofFn candidate.input.center = List.ofFn historical.input.center) :
    candidate.headSchema = historical.headSchema
```

```lean
theorem wf_head_schema_eq
    (reachable : B4TargetV6.Reachable (GeneralNominalCenteredHeadWFBoundary.boundary roles) registry root state)
    (historical candidate : Plan roles) (member : historical ∈ state.core.plans)
    (current : candidate.packet.context = state.core.erased.current.context)
    (declaration : candidate.packet.declaration = historical.packet.declaration)
    (centers : List.ofFn candidate.input.center = List.ofFn historical.input.center) :
    candidate.headSchema = historical.headSchema
```

```lean
theorem wf_candidate_actual
    (reachable : B4TargetV6.Reachable (GeneralNominalCenteredHeadWFBoundary.boundary roles) registry root state)
    (historical candidate : Plan roles) (member : historical ∈ state.core.plans)
    (current : candidate.packet.context = state.core.erased.current.context)
    (declaration : candidate.packet.declaration = historical.packet.declaration)
    (centers : List.ofFn candidate.input.center = List.ofFn historical.input.center)
    (entry : Use) (present : entry ∈ candidate.headSchema.variables) (actual : entry.mode = .actual)
    (model : Assignment) (valid : Models state model) :
    Same model entry.origin (.source (historical.binder entry.name))
```

```lean
theorem wf_candidate_readback
    (reachable : B4TargetV6.Reachable (GeneralNominalCenteredHeadWFBoundary.boundary roles) registry root state)
    (historical candidate : Plan roles) (member : historical ∈ state.core.plans)
    (current : candidate.packet.context = state.core.erased.current.context)
    (declaration : candidate.packet.declaration = historical.packet.declaration)
    (centers : List.ofFn candidate.input.center = List.ofFn historical.input.center)
    (entry : Use) (present : entry ∈ candidate.headSchema.variables) (actual : entry.mode = .actual)
    (model : Assignment) (valid : Models state model) (value) (seen : Observes model entry.origin value) :
    CommonNominalFullCarrier.Equivalent value (model (historical.binder entry.name)).1
```

```lean
theorem wf_candidate_overlap
    (reachable : B4TargetV6.Reachable (GeneralNominalCenteredHeadWFBoundary.boundary roles) registry root state)
    (historical candidate : Plan roles) (member : historical ∈ state.core.plans)
    (current : candidate.packet.context = state.core.erased.current.context)
    (declaration : candidate.packet.declaration = historical.packet.declaration)
    (centers : List.ofFn candidate.input.center = List.ofFn historical.input.center)
    (entry : Use) (present : entry ∈ candidate.headSchema.variables) (actual : entry.mode = .actual)
    (binder : candidate.binder entry.name = historical.binder entry.name)
    (model : Assignment) (valid : Models state model) :
    Same model entry.origin (.source (candidate.binder entry.name))
```

```lean
theorem wf_nonpoint_binder_eq
    (reachable : B4TargetV6.Reachable (GeneralNominalCenteredHeadWFBoundary.boundary roles) registry root state)
    (historical candidate : Plan roles) (member : historical ∈ state.core.plans)
    (current : candidate.packet.context = state.core.erased.current.context)
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
theorem wf_candidate_nonpoint_overlap
    (reachable : B4TargetV6.Reachable (GeneralNominalCenteredHeadWFBoundary.boundary roles) registry root state)
    (historical candidate : Plan roles) (member : historical ∈ state.core.plans)
    (current : candidate.packet.context = state.core.erased.current.context)
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

```lean
theorem root_extension_iff (checked : Checked registry)
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (candidate : Plan roles) (registered : candidate.input ∈ state.core.sites)
    (atRoot : candidate.packet.site.occurrence = root)
    (current : candidate.packet.context = state.core.erased.current.context)
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

```lean
theorem trace_root_identity
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (site : Site roles) (registered : site ∈ state.core.sites)
    (identity : site.occurrence.identity = root.identity) : site.occurrence = root
```

```lean
theorem wf_plan_root_identity
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (plan : Plan roles) (member : plan ∈ state.core.plans)
    (identity : plan.packet.site.occurrence.identity = root.identity) :
    plan.packet.site.occurrence = root
```

```lean
theorem wf_plan_visible
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (plan : Plan roles) (member : plan ∈ state.core.plans) :
    plan.packet.declaration ∈ registry.declarations
```

```lean
theorem candidate_root_overlap (checked : Checked registry)
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (candidate : Plan roles) (registered : candidate.input ∈ state.core.sites)
    (atRoot : candidate.packet.site.occurrence = root)
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

```lean
theorem registered_producers
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    (∀ site ∈ state.core.sites, root.identity ≤ site.occurrence.identity) ∧
    (∀ plan ∈ state.core.plans, root.identity ≤ plan.packet.site.occurrence.identity ∧
      plan.packet.declaration ∈ registry.declarations)
```

```lean
theorem emitted_not_root
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (plan : Plan roles) (registered : plan ∈ state.core.plans)
    (site : Site roles) (emitted : site ∈ plan.emitted) : site.occurrence ≠ root
```

```lean
theorem trace_site_unique (checked : Checked registry)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (first last : Site roles) (one : first ∈ state.core.sites) (two : last ∈ state.core.sites)
    (same : first.occurrence = last.occurrence) : first = last
```

```lean
theorem wf_site_unique (checked : Checked registry)
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (first last : Site roles) (one : first ∈ state.core.sites) (two : last ∈ state.core.sites)
    (same : first.occurrence = last.occurrence) : first = last
```

```lean
theorem site_origin (path : B4Target.Steps (Step registry root) before after) :
    ∀ site ∈ after.core.sites, site ∈ before.core.sites ∨ ∃ plan ∈ after.core.plans, site ∈ plan.emitted
```

```lean
theorem initial_site_origin
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (site : Site roles) (member : site ∈ state.core.sites) :
    site = rootSite context.state.seed root ∨ ∃ plan ∈ state.core.plans, site ∈ plan.emitted
```

```lean
theorem plan_seed
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    ∀ plan ∈ state.core.plans, plan.packet.context.state.seed = context.state.seed
```

```lean
theorem root_not_eight
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (index : Fin (roles root.demand.role).arity) :
    (rootSite context.state.seed root).center index ≠
      fresh context.state.seed invocation declaration 8 owner position
```

```lean
theorem purpose_eight_site_binder
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (site : Site roles) (member : site ∈ state.core.sites)
    (index : Fin (roles site.occurrence.demand.role).arity)
    (center : site.center index = fresh context.state.seed invocation declaration 8 owner position) :
    ∃ plan ∈ state.core.plans, ∃ name, plan.binder name = site.center index
```

```lean
theorem purpose_eight_site_needed
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (site : Site roles) (member : site ∈ state.core.sites)
    (index : Fin (roles site.occurrence.demand.role).arity)
    (center : site.center index = fresh context.state.seed invocation declaration 8 owner position) :
    ∃ plan ∈ state.core.plans, ∃ name, GeneralNominalSharedCaptures.Needed plan.packet name ∧ plan.binder name = site.center index
```

```lean
theorem purpose_eight_site_fits
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (site : Site roles) (member : site ∈ state.core.sites)
    (index : Fin (roles site.occurrence.demand.role).arity)
    (center : site.center index = fresh context.state.seed invocation declaration 8 owner position)
    (valid : Models state model) :
    ∃ plan ∈ state.core.plans, ∃ name, GeneralNominalSharedCaptures.Needed plan.packet name ∧
      plan.binder name = site.center index ∧
      GeneralNominalCaptureMerges.Fits model
        ((GeneralNominalPacketSupport.capture plan.packet).inputs name) (model (site.center index)).1
```

```lean
theorem trace_sources_separate
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (high : 7 ≤ purpose) :
    fresh context.state.seed invocation declaration purpose owner position ∉
      GeneralNominalState.sources state.core.erased.current.context.state
```

```lean
theorem trace_sites_separate
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (high : 7 ≤ purpose) :
    ∀ site ∈ state.core.erased.current.sites,
      fresh context.state.seed invocation declaration purpose owner position ∉ rawSiteSources site
```

```lean
theorem wf_sources_separate
    (reachable : B4TargetV6.Reachable (GeneralNominalCenteredHeadWFBoundary.boundary roles) registry root state)
    (high : 7 ≤ purpose) :
    fresh state.core.erased.current.context.state.seed invocation declaration purpose owner position ∉
      GeneralNominalState.sources state.core.erased.current.context.state
```

```lean
theorem wf_sites_separate
    (reachable : B4TargetV6.Reachable (GeneralNominalCenteredHeadWFBoundary.boundary roles) registry root state)
    (site : GeneralNominalDemandMerging.Site roles) (member : site ∈ state.core.erased.current.sites)
    (high : 7 ≤ purpose) :
    fresh state.core.erased.current.context.state.seed invocation declaration purpose owner position ∉
      rawSiteSources site
```
