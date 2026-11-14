# Cycle183 public theorem signatures

All are auxiliary producer/reduction/regression results. See source for proofs and final report for scope.

## GeneralNominalOriginAgreement183

```lean
theorem uniform_site_fits
    (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (site : Site roles) (member : site ∈ state.sites)
    (index : Fin (roles site.occurrence.demand.role).arity)
    (center : site.center index = fresh state.erased.current.context.state.seed
      invocation declaration 8 owner position) :
    ∃ plan ∈ state.plans, ∃ name, GeneralNominalSharedCaptures.Needed plan.packet name ∧
      plan.binder name = site.center index ∧
      ∀ model, Models state model → GeneralNominalCaptureMerges.Fits model
        ((GeneralNominalPacketSupport.capture plan.packet).inputs name)
        (model (site.center index)).1
```

```lean
theorem source_agreement_iff (source : ActualBinder state name historical)
    (valid : Models state model) :
    Same model candidate (.source name) ↔ Same model candidate historical
```

```lean
theorem actual_origins_agree (first : ActualBinder state name one)
    (last : ActualBinder state name two) (valid : Models state model) :
    Same model one two
```

```lean
theorem uniform_source_agreement_iff (source : ActualBinder state name historical) :
    (∀ model, Models state model → Same model candidate (.source name)) ↔
    (∀ model, Models state model → Same model candidate historical)
```

```lean
theorem readback_agreement_iff (source : ActualBinder state name historical)
    (valid : Models state model) :
    ((∃ value, Observes model candidate value) ∧
      ∀ value, Observes model candidate value → Equivalent value (model name).1) ↔
    Same model candidate historical
```

```lean
theorem extension_iff_historical (arguments : Fin count → NominalArgument)
    (historical : Fin count → Origin) (previous : Assignment) (valid : Models state previous)
    (linked : ∀ i, (arguments i).argument.endpoints.1 ∈ fullSources state ∧
      (arguments i).argument.endpoints.2 ∈ fullSources state ∧
      originSource (arguments i).origin ∈ fullSources state)
    (provenance : ∀ i, (arguments i).argument.center ∈ fullSources state →
      ActualBinder state (arguments i).argument.center (historical i)) :
    (∃ extended, Models state extended ∧
      (∀ name ∈ fullSources state, extended name = previous name) ∧
      ∀ i, (arguments i).Holds extended) ↔
    (∀ i, ∃ actual, Observes previous (arguments i).origin actual) ∧
    (∀ i actual, Observes previous (arguments i).origin actual →
      GeneralNominalCaptureMerges.Fits previous (arguments i).argument.endpoints actual) ∧
    (∀ i j first last, (arguments i).argument.center = (arguments j).argument.center →
      Observes previous (arguments i).origin first → Observes previous (arguments j).origin last →
      Equivalent first last) ∧
    (∀ i, (arguments i).argument.center ∈ fullSources state →
      Same previous (arguments i).origin (historical i))
```

## GeneralNominalCaptureCoverage183

```lean
theorem inspect_covers (state : GeneralNominalState.State) (query : Query)
      (bounds : Bounds state) (origin : Option Origin)
      (finished : Finished (inspect state query bounds origin))
      (name : Nat) (member : name ∈ names query) :
      ∃ captured ∈ (inspect state query bounds origin).captures, captured.name = name
```

```lean
theorem many_covers (state : GeneralNominalState.State) (queries : List Query)
      (bounds : List (Bounds state)) (origins : Nat → Option Origin) (offset : Nat)
      (finished : Finished (inspectMany state queries bounds origins offset))
      (name : Nat) (member : name ∈ manyNames queries) :
      ∃ captured ∈ (inspectMany state queries bounds origins offset).captures, captured.name = name
```

```lean
theorem inspect_name_iff (state : GeneralNominalState.State) (query : Query)
    (bounds : Bounds state) (origin : Option Origin)
    (finished : Finished (inspect state query bounds origin)) (name : Nat) :
    (∃ captured ∈ (inspect state query bounds origin).captures, captured.name = name) ↔
      name ∈ names query
```

```lean
theorem many_name_iff (state : GeneralNominalState.State) (queries : List Query)
    (bounds : List (Bounds state)) (origins : Nat → Option Origin) (offset : Nat)
    (finished : Finished (inspectMany state queries bounds origins offset)) (name : Nat) :
    (∃ captured ∈ (inspectMany state queries bounds origins offset).captures, captured.name = name) ↔
      name ∈ manyNames queries
```

## GeneralNominalQueryProvenance183

```lean
theorem installable_finished (plan : Plan roles)
    (enabled : GeneralNominalFeedbackSteps.Installable registry state.erased.current plan.packet) :
    Finished (headInspection plan)
```

```lean
theorem registered_finished
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    ∀ plan ∈ state.plans, Finished (headInspection plan)
```

```lean
theorem registered_query_actual
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (plan : Plan roles) (registered : plan ∈ state.plans) (name : Nat)
    (named : name ∈ queryNames plan) :
    ∃ origin, ActualBinder state (plan.binder name) origin
```

```lean
theorem ground_query_actual
    (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (plan : Plan roles) (registered : plan ∈ state.plans) (name : Nat)
    (named : name ∈ queryNames plan) :
    ∃ origin, ActualBinder state (plan.binder name) origin
```

```lean
theorem uniform_ground_query_readback
    (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (plan : Plan roles) (registered : plan ∈ state.plans) (name : Nat)
    (named : name ∈ queryNames plan) :
    ∃ origin, ActualBinder state (plan.binder name) origin ∧
      ∀ model, Models state model → GeneralNominalOriginTerms.Same model origin (.source (plan.binder name))
```

## GeneralNominalCompleteNames183

```lean
theorem inspect_complete (state : GeneralNominalState.State) (query : Query)
      (bounds : Bounds state) (origin : Option Origin)
      (finished : Finished (inspect state query bounds origin)) : Complete query
```

```lean
theorem many_complete (state : GeneralNominalState.State) (queries : List Query)
      (bounds : List (Bounds state)) (origins : Nat → Option Origin) (offset : Nat)
      (finished : Finished (inspectMany state queries bounds origins offset)) :
      ∀ query ∈ queries, Complete query
```

```lean
theorem translated_names (constructors : Constructors) (interpretation : Interpretation)
    (pattern : Pattern) (complete : Complete (translate constructors interpretation pattern))
    (name : Nat) (member : name ∈ pattern.variables) :
    name ∈ names (translate constructors interpretation pattern)
```

```lean
theorem translated_many_names (constructors : Constructors) (interpretation : Interpretation)
    (patterns : List Pattern)
    (complete : ∀ pattern ∈ patterns, Complete (translate constructors interpretation pattern))
    (name : Nat) (member : name ∈ variablesArgs patterns) :
    name ∈ manyNames (patterns.map (translate constructors interpretation))
```

```lean
theorem finished_translated_names (state : GeneralNominalState.State)
    (interpretation : Interpretation) (patterns : List Pattern)
    (bounds : List (Bounds state)) (origins : Nat → Option Origin) (offset : Nat)
    (finished : Finished (inspectMany state (patterns.map (translate state.constructors interpretation)) bounds origins offset))
    (name : Nat) (member : name ∈ variablesArgs patterns) :
    name ∈ manyNames (patterns.map (translate state.constructors interpretation))
```

```lean
theorem declaration_input_capture (state : GeneralNominalState.State)
    (interpretation : Interpretation) (declaration : GeneralDeclarations.Declaration)
    (bounds : List (Bounds state)) (origins : Nat → Option Origin) (offset : Nat)
    (finished : Finished (inspectMany state (queries state interpretation declaration) bounds origins offset))
    (name : Nat) (member : name ∈ declaration.inputNames) :
    ∃ captured ∈ (inspectMany state (queries state interpretation declaration) bounds origins offset).captures,
      captured.name = name
```

## GeneralNominalRegisteredCoverage183

```lean
theorem registered_input_actual
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (plan : Plan roles) (registered : plan ∈ state.plans) (name : Nat)
    (named : name ∈ plan.packet.declaration.inputNames) :
    ∃ origin, ActualBinder state (plan.binder name) origin
```

```lean
theorem registered_capture_actual
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (plan : Plan roles) (registered : plan ∈ state.plans) (name : Nat)
    (needed : name ∈ plan.packet.declaration.inputNames ∨ GeneralNominalSharedCaptures.Needed plan.packet name) :
    ∃ origin, ActualBinder state (plan.binder name) origin
```

```lean
theorem ground_capture_actual
    (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (plan : Plan roles) (registered : plan ∈ state.plans) (name : Nat)
    (needed : name ∈ plan.packet.declaration.inputNames ∨ GeneralNominalSharedCaptures.Needed plan.packet name) :
    ∃ origin, ActualBinder state (plan.binder name) origin
```

```lean
theorem uniform_ground_capture_readback
    (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (plan : Plan roles) (registered : plan ∈ state.plans) (name : Nat)
    (needed : name ∈ plan.packet.declaration.inputNames ∨ GeneralNominalSharedCaptures.Needed plan.packet name) :
    ∃ origin, ActualBinder state (plan.binder name) origin ∧
      ∀ model, Models state model → GeneralNominalOriginTerms.Same model origin (.source (plan.binder name))
```

```lean
theorem uniform_ground_site_readback
    (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (site : Site roles) (member : site ∈ state.sites)
    (index : Fin (roles site.occurrence.demand.role).arity)
    (center : site.center index = fresh state.erased.current.context.state.seed
      invocation declaration 8 owner position) :
    ∃ origin, ActualBinder state (site.center index) origin ∧
      ∀ model, Models state model → GeneralNominalOriginTerms.Same model origin (.source (site.center index))
```

## GeneralNominalRawSupport183

```lean
theorem packet_private_pool
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    ∀ packet ∈ state.erased.current.packets,
      GeneralNominalState.sources packet.privateContext.state ⊆ pool registry context root limit
```

```lean
theorem packet_seed
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    ∀ packet ∈ state.erased.current.packets, packet.context.state.seed = context.state.seed
```

```lean
theorem capture_output_separate (packet : GeneralNominalSaturationState.Packet roles)
    (high : 7 ≤ purpose) (name : Nat) :
    fresh packet.context.state.seed invocation declaration purpose owner position ≠
      (GeneralNominalPacketSupport.capture packet).outputs name
```

```lean
theorem capture_inputs_separate (packet : GeneralNominalSaturationState.Packet roles)
    (high : 7 ≤ purpose)
    (outside : fresh packet.context.state.seed invocation declaration purpose owner position ∉
      GeneralNominalState.sources packet.context.state) (name : Nat) :
    fresh packet.context.state.seed invocation declaration purpose owner position ≠
      ((GeneralNominalPacketSupport.capture packet).inputs name).1 ∧
    fresh packet.context.state.seed invocation declaration purpose owner position ≠
      ((GeneralNominalPacketSupport.capture packet).inputs name).2
```

```lean
theorem historical_capture_separate
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (packet : GeneralNominalSaturationState.Packet roles) (member : packet ∈ state.erased.current.packets)
    (high : 7 ≤ purpose) (name : Nat) :
    fresh context.state.seed invocation declaration purpose owner position ≠
      (GeneralNominalPacketSupport.capture packet).outputs name ∧
    fresh context.state.seed invocation declaration purpose owner position ≠
      ((GeneralNominalPacketSupport.capture packet).inputs name).1 ∧
    fresh context.state.seed invocation declaration purpose owner position ≠
      ((GeneralNominalPacketSupport.capture packet).inputs name).2
```

```lean
theorem historical_private_separate
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (packet : GeneralNominalSaturationState.Packet roles) (member : packet ∈ state.erased.current.packets)
    (high : 7 ≤ purpose) :
    fresh context.state.seed invocation declaration purpose owner position ∉
      GeneralNominalState.sources packet.privateContext.state
```

## GeneralNominalGroundRawSupport183

```lean
theorem capture_separate
    (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (packet : GeneralNominalSaturationState.Packet roles) (member : packet ∈ state.erased.current.packets)
    (high : 7 ≤ purpose) (name : Nat) :
    fresh state.erased.current.context.state.seed invocation declaration purpose owner position ≠
      (GeneralNominalPacketSupport.capture packet).outputs name ∧
    fresh state.erased.current.context.state.seed invocation declaration purpose owner position ≠
      ((GeneralNominalPacketSupport.capture packet).inputs name).1 ∧
    fresh state.erased.current.context.state.seed invocation declaration purpose owner position ≠
      ((GeneralNominalPacketSupport.capture packet).inputs name).2
```

```lean
theorem private_separate
    (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (packet : GeneralNominalSaturationState.Packet roles) (member : packet ∈ state.erased.current.packets)
    (high : 7 ≤ purpose) :
    fresh state.erased.current.context.state.seed invocation declaration purpose owner position ∉
      GeneralNominalState.sources packet.privateContext.state
```

## GeneralNominalCoverageRegression183

```lean
theorem terminal_has_input : 37 ∈ terminal.inputNames
```

```lean
theorem terminal_has_no_children : terminal.requirements = []
```

```lean
theorem terminal_finished (state : GeneralNominalState.State) (interpretation : Interpretation)
    (bounds : Bounds state) (origins : Nat → Option Origin) :
    Finished (inspectMany state (queries state interpretation terminal) [bounds] origins 0)
```

```lean
theorem terminal_input_captured (state : GeneralNominalState.State) (interpretation : Interpretation)
    (bounds : Bounds state) (origins : Nat → Option Origin) :
    ∃ captured ∈ (inspectMany state (queries state interpretation terminal) [bounds] origins 0).captures,
      captured.name = 37
```
