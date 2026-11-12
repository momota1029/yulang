# Cycle137 theorem signatures

日本語の主張・検証範囲は dots-cycle-137.md。以下は量化子と前提を省略しない型一覧。
証明本体は対応する Lean ファイルを参照。範囲の限定や補助定理を主定理の達成数に読み替えない。

## GeneralDictionaryCurrentContextReplay

```lean
theorem instance_replay (registry : Registry)
    (before middle : GeneralNominalCandidates.Context) (next : Observation middle.state)
    (growth : GeneralDictionaryOrdinaryTrace.Extension before middle)
    (root : Occurrence roles) (key : Nat) (children : List (Occurrence roles))
    (same : PreservesAt registry middle next root) (model : Assignment)
    (middleValid : GeneralNominalState.Models middle.state model)
    (finalValid : GeneralNominalState.Models (reobserve middle next).state model)
    (old : GeneralDictionaryRecursiveEvidence.Instance registry before model root key children) :
    GeneralDictionaryRecursiveEvidence.Instance registry (reobserve middle next) model root key children
```

```lean
theorem sourceFormed_recorded_current_instance (registry : Registry) (root : Occurrence roles)
    (state : State roles) (formed : GeneralNominalFeedbackSteps.SourceFormed registry root state)
    (packet : Packet roles) (recorded : packet ∈ state.packets)
    (middle : GeneralNominalCandidates.Context) (next : Observation middle.state)
    (growth : GeneralDictionaryOrdinaryTrace.Extension packet.context middle)
    (current : state.context = reobserve middle next)
    (same : PreservesAt registry middle next packet.site.occurrence)
    (model : Assignment) (valid : Models state model)
    (middleValid : GeneralNominalState.Models middle.state model) :
    GeneralDictionaryRecursiveEvidence.Instance registry state.context model
      packet.site.occurrence packet.declaration.id packet.children
```

```lean
theorem sourceFormed_recorded_current_evidence (registry : Registry) (root : Occurrence roles)
    (state : State roles) (formed : GeneralNominalFeedbackSteps.SourceFormed registry root state)
    (packet : Packet roles) (recorded : packet ∈ state.packets)
    (middle : GeneralNominalCandidates.Context) (next : Observation middle.state)
    (growth : GeneralDictionaryOrdinaryTrace.Extension packet.context middle)
    (current : state.context = reobserve middle next)
    (same : PreservesAt registry middle next packet.site.occurrence)
    (model : Assignment) (valid : Models state model)
    (middleValid : GeneralNominalState.Models middle.state model) (dictionaries : List Payload)
    (given : CommonRoleOutermostResolver.All₂
      (GeneralDictionaryRecursiveEvidence.Evidence registry state.context model) packet.children dictionaries) :
    GeneralDictionaryRecursiveEvidence.Evidence registry state.context model packet.site.occurrence
      (.node packet.declaration.id dictionaries)
```

```lean
theorem refreshed_parent_after_ordinary_trace (after : State GeneralDeclarationExamples.roles)
    (path : B4Target.Steps
      (GeneralDictionaryOrdinaryTrace.OrdinaryStep GeneralNominalFeedbackObstruction.registry
        GeneralNominalFeedbackObstruction.root) GeneralNominalFeedbackRefresh.refreshed after)
    (model : Assignment) (valid : Models after model) :
    GeneralDictionaryRecursiveEvidence.Instance GeneralNominalFeedbackObstruction.registry
      after.context model GeneralNominalFeedbackObstruction.root 2 [GeneralNominalFeedbackObstruction.child]
```

```lean
theorem refreshed_tail_execution (after : State GeneralDeclarationExamples.roles)
    (path : B4Target.Steps
      (GeneralDictionaryOrdinaryTrace.OrdinaryStep GeneralNominalFeedbackObstruction.registry
        GeneralNominalFeedbackObstruction.root) GeneralNominalFeedbackRefresh.refreshed after) :
    B4Target.Steps (GeneralNominalFeedbackSteps.Step GeneralNominalFeedbackObstruction.registry
      GeneralNominalFeedbackObstruction.root) GeneralNominalFeedbackObstruction.initialState after
```

```lean
theorem refreshed_parent_nonvacuous :
    Models GeneralNominalFeedbackRefresh.refreshed GeneralNominalFeedbackObstruction.model ∧
    GeneralDictionaryRecursiveEvidence.Instance GeneralNominalFeedbackObstruction.registry
      GeneralNominalFeedbackRefresh.refreshed.context GeneralNominalFeedbackObstruction.model
      GeneralNominalFeedbackObstruction.root 2 [GeneralNominalFeedbackObstruction.child] ∧
    GeneralNominalFeedbackK2.Local GeneralNominalFeedbackObstruction.registry
      GeneralNominalFeedbackRefresh.refreshed GeneralNominalFeedbackObstruction.child .rejected
```

## GeneralDictionaryFinishedEvidence

```lean
theorem report_finished (context : Context) (next : Observation context.state)
    (view : next.view = context.state.view)
    (refinement : GeneralNominalRefinements.Refines context.state (reobserve context next).state)
    (declaration : Declaration) (bounds : List (GeneralNominalInspection.Bounds context.state))
    (finished : Finished (report context declaration bounds)) :
    report (reobserve context next) declaration bounds = transferReport context next (report context declaration bounds)
```

```lean
theorem instance_refinement (registry : Registry) (context : Context) (next : Observation context.state)
    (view : next.view = context.state.view)
    (refinement : GeneralNominalRefinements.Refines context.state (reobserve context next).state)
    (model : Assignment) (valid : GeneralNominalState.Models (reobserve context next).state model)
    (root : Occurrence roles) (key : Nat) (children : List (Occurrence roles))
    (old : GeneralDictionaryRecursiveEvidence.Instance registry context model root key children) :
    GeneralDictionaryRecursiveEvidence.Instance registry (reobserve context next) model root key children
```

```lean
theorem evidence_refinement (registry : Registry) (context : Context) (next : Observation context.state)
    (view : next.view = context.state.view)
    (refinement : GeneralNominalRefinements.Refines context.state (reobserve context next).state)
    (model : Assignment) (valid : GeneralNominalState.Models (reobserve context next).state model)
    (root : Occurrence roles) (payload : GeneralDictionaryReadback.Payload)
    (old : GeneralDictionaryRecursiveEvidence.Evidence registry context model root payload) :
    GeneralDictionaryRecursiveEvidence.Evidence registry (reobserve context next) model root payload
```

```lean
theorem recorded_refresh (registry : Registry) (root : Occurrence roles)
    (before : State roles) (formed : GeneralNominalFeedbackSteps.SourceFormed registry root before)
    (packet : Packet roles) (recorded : packet ∈ before.packets)
    (growth : GeneralDictionaryOrdinaryTrace.Extension packet.context before.context)
    (next : Observation before.context.state) (view : next.view = before.context.state.view)
    (refresh : GeneralNominalCycleSteps.Refresh before (reobserve before.context next))
    (model : Assignment) (valid : Models (regenerate before (reobserve before.context next)) model) :
    GeneralDictionaryRecursiveEvidence.Instance registry (reobserve before.context next) model
      packet.site.occurrence packet.declaration.id packet.children
```

## GeneralDictionaryFinishedInspection

```lean
theorem inspect_finished (context : Context) (next : Observation context.state)
    (view : next.view = context.state.view)
    (refinement : GeneralNominalRefinements.Refines context.state (reobserve context next).state)
    (query : Query) (bounds : Bounds context.state) (origin : Option Origin)
    (finished : Finished (inspect context.state query bounds origin)) :
    inspect (reobserve context next).state query bounds origin =
      transferReport context next (inspect context.state query bounds origin)
```

```lean
theorem inspectMany_finished (context : Context) (next : Observation context.state)
    (view : next.view = context.state.view)
    (refinement : GeneralNominalRefinements.Refines context.state (reobserve context next).state)
    (queries : List Query) (bounds : List (Bounds context.state)) (origins : Nat → Option Origin) (index : Nat)
    (finished : Finished (inspectMany context.state queries bounds origins index)) :
    inspectMany (reobserve context next).state queries bounds origins index =
      transferReport context next (inspectMany context.state queries bounds origins index)
```

## GeneralDictionaryFinishedInspectionExamples

```lean
theorem nested_finished : Finished (inspect state query bounds none)
```

```lean
theorem footprint_not_occupied :
    ¬ (∀ slot ∈ footprint state query bounds, ∃ descriptor, state.nominals slot = some descriptor)
```

```lean
theorem nested_survives (next : Observation state) (view : next.view = state.view)
    (refinement : GeneralNominalRefinements.Refines state (reobserve context next).state) :
    inspect (reobserve context next).state query bounds none =
      transferReport context next (inspect state query bounds none)
```

```lean
theorem nonvacuous_nested : GeneralNominalState.Models state model ∧
    Finished (inspect state query bounds none) ∧
    ¬ (∀ slot ∈ footprint state query bounds, ∃ descriptor, state.nominals slot = some descriptor)
```

## GeneralDictionaryFinishedRefresh

```lean
theorem finished_nominal_lower (state : GeneralNominalState.State) (name : Nat)
    (patterns : List Query) (bounds : Bounds state) (origin : Option Origin)
    (finished : Finished (inspect state (.nominal name patterns) bounds origin)) :
    ∃ descriptor, state.nominals bounds.1 = some descriptor
```

```lean
theorem finished_nominal_upper (state : GeneralNominalState.State) (name : Nat)
    (patterns : List Query) (bounds : Bounds state) (origin : Option Origin)
    (finished : Finished (inspect state (.nominal name patterns) bounds origin)) :
    ∃ descriptor, state.nominals bounds.2 = some descriptor
```

```lean
theorem variable_footprints (state : GeneralNominalState.State)
    (groups : List (List Nat)) (bounds : List (Bounds state)) :
    footprints state (groups.map Query.variables) bounds = []
```

```lean
theorem flat_nominal_footprint (state : GeneralNominalState.State) (name : Nat)
    (groups : List (List Nat)) (bounds : Bounds state) :
    footprint state (.nominal name (groups.map Query.variables)) bounds = [bounds.1,bounds.2]
```

```lean
theorem flat_nominal_finished_preserved (context : Context) (next : Observation context.state)
    (view : next.view = context.state.view)
    (refinement : GeneralNominalRefinements.Refines context.state (reobserve context next).state)
    (name : Nat) (groups : List (List Nat)) (bounds : Bounds context.state) (origin : Option Origin)
    (finished : Finished (inspect context.state (.nominal name (groups.map Query.variables)) bounds origin)) :
    inspect (reobserve context next).state (.nominal name (groups.map Query.variables)) bounds origin =
      transferReport context next (inspect context.state (.nominal name (groups.map Query.variables)) bounds origin)
```

## GeneralDictionaryFinishedTrace

`descriptor_changing_step` と `current_parent_without_guard` は、このmoduleの `Actual` 名前空間内。

```lean
theorem step_feedback (registry : Registry) (root : Occurrence roles)
    (before after : State roles) (step : Step registry root before after) :
    GeneralNominalFeedbackSteps.Step registry root before after
```

```lean
theorem trace_feedback (registry : Registry) (root : Occurrence roles)
    (before after : State roles) (path : B4Target.Steps (Step registry root) before after) :
    B4Target.Steps (GeneralNominalFeedbackSteps.Step registry root) before after
```

```lean
theorem step_instance (registry : Registry) (root site : Occurrence roles)
    (before after : State roles) (step : Step registry root before after)
    (model : Assignment) (valid : Models after model) (key : Nat) (children : List (Occurrence roles))
    (old : GeneralDictionaryRecursiveEvidence.Instance registry before.context model site key children) :
    GeneralDictionaryRecursiveEvidence.Instance registry after.context model site key children
```

```lean
theorem trace_instance (registry : Registry) (root site : Occurrence roles)
    (before after : State roles) (path : B4Target.Steps (Step registry root) before after)
    (model : Assignment) (valid : Models after model) (key : Nat) (children : List (Occurrence roles))
    (old : GeneralDictionaryRecursiveEvidence.Instance registry before.context model site key children) :
    GeneralDictionaryRecursiveEvidence.Instance registry after.context model site key children
```

```lean
theorem trace_evidence (registry : Registry) (root site : Occurrence roles)
    (before after : State roles) (path : B4Target.Steps (Step registry root) before after)
    (model : Assignment) (valid : Models after model) (payload : GeneralDictionaryReadback.Payload)
    (old : GeneralDictionaryRecursiveEvidence.Evidence registry before.context model site payload) :
    GeneralDictionaryRecursiveEvidence.Evidence registry after.context model site payload
```

```lean
theorem recorded_trace_instance (registry : Registry) (root : Occurrence roles)
    (before after : State roles) (formed : GeneralNominalFeedbackSteps.SourceFormed registry root before)
    (packet : Packet roles) (recorded : packet ∈ before.packets)
    (growth : GeneralDictionaryOrdinaryTrace.Extension packet.context before.context)
    (path : B4Target.Steps (Step registry root) before after)
    (model : Assignment) (valid : Models after model) :
    GeneralDictionaryRecursiveEvidence.Instance registry after.context model
      packet.site.occurrence packet.declaration.id packet.children
```

```lean
theorem descriptor_changing_step : Step registry root installed refreshed
```

```lean
theorem current_parent_without_guard (m : Assignment) (valid : Models refreshed m) :
    GeneralDictionaryRecursiveEvidence.Instance registry refreshedContext m root 2 [child]
```

## GeneralDictionaryInspectionLocality

```lean
@[simp] theorem variables_footprint (state : GeneralNominalState.State) (names : List Nat)
    (bounds : Bounds state) : footprint state (.variables names) bounds = []
```

```lean
@[simp] theorem transfer_append (context : Context) (next : Observation context.state)
    (first last : Report context.state) :
    transferReport context next (first.append last) =
      (transferReport context next first).append (transferReport context next last)
```

```lean
@[simp] theorem transfer_visit (context : Context) (next : Observation context.state)
    (bounds : Bounds context.state) (origin : Option Origin) (test : Test) (value : Report context.state) :
    transferReport context next (Report.visit bounds origin test value) =
      @Report.visit (reobserve context next).state bounds origin test (transferReport context next value)
```

```lean
theorem inspect_local (context : Context) (next : Observation context.state)
      (view : next.view = context.state.view)
      (query : Query) (bounds : Bounds context.state) (origin : Option Origin)
      (same : ∀ slot ∈ footprint context.state query bounds,
        next.nominals slot = context.state.nominals slot) :
      inspect (reobserve context next).state query bounds origin =
        transferReport context next (inspect context.state query bounds origin)
```

```lean
theorem inspectMany_local (context : Context) (next : Observation context.state)
      (view : next.view = context.state.view)
      (queries : List Query) (bounds : List (Bounds context.state)) (origins : Nat → Option Origin) (index : Nat)
      (same : ∀ slot ∈ footprints context.state queries bounds,
        next.nominals slot = context.state.nominals slot) :
      inspectMany (reobserve context next).state queries bounds origins index =
        transferReport context next (inspectMany context.state queries bounds origins index)
```

```lean
theorem report_local (context : Context) (next : Observation context.state)
    (view : next.view = context.state.view) (declaration : GeneralDeclarations.Declaration)
    (bounds : List (Bounds context.state))
    (same : ∀ slot ∈ footprints context.state
      (GeneralNominalInspection.queries context.state context.interpretation declaration) bounds,
      next.nominals slot = context.state.nominals slot) :
    GeneralNominalRecursiveCandidates.report (reobserve context next) declaration bounds =
      transferReport context next (GeneralNominalRecursiveCandidates.report context declaration bounds)
```

```lean
theorem preservesAt_of_footprint (registry : GeneralDeclarations.Registry) (context : Context)
    (next : Observation context.state) (view : next.view = context.state.view)
    (root : GeneralSourceDictionaries.Occurrence roles)
    (same : FootprintAt registry context next root) : PreservesAt registry context next root
```

```lean
theorem instance_of_footprint (registry : GeneralDeclarations.Registry) (context : Context)
    (next : Observation context.state) (view : next.view = context.state.view)
    (model : GeneralNominalCommonBridge.Assignment) (root : GeneralSourceDictionaries.Occurrence roles)
    (key : Nat) (children : List (GeneralSourceDictionaries.Occurrence roles))
    (same : FootprintAt registry context next root)
    (valid : GeneralNominalState.Models (reobserve context next).state model)
    (old : GeneralDictionaryRecursiveEvidence.Instance registry context model root key children) :
    GeneralDictionaryRecursiveEvidence.Instance registry (reobserve context next) model root key children
```

```lean
theorem node_of_footprint (registry : GeneralDeclarations.Registry) (context : Context)
    (next : Observation context.state) (view : next.view = context.state.view)
    (model : GeneralNominalCommonBridge.Assignment) (root : GeneralSourceDictionaries.Occurrence roles)
    (key : Nat) (children : List (GeneralSourceDictionaries.Occurrence roles))
    (dictionaries : List GeneralDictionaryReadback.Payload)
    (same : FootprintAt registry context next root)
    (valid : GeneralNominalState.Models (reobserve context next).state model)
    (old : GeneralDictionaryRecursiveEvidence.Instance registry context model root key children)
    (given : CommonRoleOutermostResolver.All₂
      (GeneralDictionaryRecursiveEvidence.Evidence registry (reobserve context next) model)
      children dictionaries) :
    GeneralDictionaryRecursiveEvidence.Evidence registry (reobserve context next) model root
      (.node key dictionaries)
```

## GeneralDictionaryInspectionLocalityExamples

```lean
theorem parent_footprint :
    footprints installed.context.state
      (GeneralNominalInspection.queries installed.context.state installed.context.interpretation declaration)
      [(⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩)] = [⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩]
```

```lean
theorem parent_footprint_agrees : FootprintAt registry installed.context observation root
```

```lean
theorem current_parent_from_footprint (m : Assignment) (valid : Models refreshed m) :
    GeneralDictionaryRecursiveEvidence.Instance registry refreshedContext m root 2 [child]
```

```lean
theorem nonvacuous_parent_from_footprint :
    Models refreshed model ∧
      GeneralDictionaryRecursiveEvidence.Instance registry refreshedContext model root 2 [child]
```

```lean
theorem nested_nonpoint_footprint :
    footprint installed.context.state (.nominal 0 [.nominal 0 [.variables [0]]]) (⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩) =
      [⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩,⟨2,by decide +kernel⟩,⟨3,by decide +kernel⟩,
        ⟨2,by decide +kernel⟩,⟨3,by decide +kernel⟩]
```

```lean
theorem inspected_child_report_changes :
    (GeneralNominalRecursiveInspection.inspect installed.context.state
      (.nominal 0 []) (⟨2,by decide +kernel⟩,⟨2,by decide +kernel⟩) none).blocked ≠
    (GeneralNominalRecursiveInspection.inspect refreshedContext.state
      (.nominal 0 []) (⟨2,by decide +kernel⟩,⟨2,by decide +kernel⟩) none).blocked
```

## GeneralDictionaryInspectionTransport

```lean
@[simp] theorem transferred_bindings (context : Context) (next : Observation context.state)
    (value : Report context.state) :
    bindings (reobserve context next).state (transferReport context next value) =
      bindings context.state value
```

```lean
@[simp] theorem transferred_selfChecks (context : Context) (next : Observation context.state)
    (value : Report context.state) :
    selfChecks (reobserve context next).state (transferReport context next value) =
      selfChecks context.state value
```

```lean
@[simp] theorem transferred_finished (context : Context) (next : Observation context.state)
    (value : Report context.state) :
    Finished (transferReport context next value) ↔ Finished value
```

```lean
@[simp] theorem transferred_projection (context : Context) (next : Observation context.state)
    (value : Report context.state) (model : Assignment) :
    ProjectionModels (reobserve context next).state (transferReport context next value) model ↔
      ProjectionModels context.state value model
```

```lean
@[simp] theorem transferred_materialization (context : Context) (next : Observation context.state)
    (value : Report context.state) (declaration : Declaration)
    (captured : GeneralDeclarationDemands.Capture)
    (schema : GeneralNominalMaterialization.Schema) (model : Assignment) :
    GeneralNominalMaterialization.Models (reobserve context next).state declaration captured
      (transferReport context next value) schema model ↔
    GeneralNominalMaterialization.Models context.state declaration captured value schema model
```

```lean
theorem nominal_unary_report (context : Context) (next : Observation context.state)
    (declaration : Declaration) (slot : Fin context.state.base.slots)
    (descriptor : GeneralNominalState.Descriptor context.state.base.slots)
    (old : context.state.nominals slot = some descriptor)
    (kept : next.nominals slot = some descriptor)
    (binder : Nat) (bounds : GeneralNominalInspection.Bounds context.state)
    (parameters : descriptor.arguments = [.type bounds])
    (query : GeneralNominalInspection.queries context.state context.interpretation declaration =
      [.nominal descriptor.declaration.name [.variables [binder]]]) :
    report (reobserve context next) declaration [(slot,slot)] =
      transferReport context next (report context declaration [(slot,slot)])
```

```lean
theorem generated_eq (registry : Registry) (context : Context) (next : Observation context.state)
    (root : Occurrence roles) (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (bounds : List (GeneralNominalInspection.Bounds context.state))
    (same : report (reobserve context next) declaration bounds =
      transferReport context next (report context declaration bounds)) :
    generated registry (reobserve context next) root declaration checked bounds =
      generated registry context root declaration checked bounds
```

```lean
theorem branch_of_report (registry : Registry) (context : Context) (next : Observation context.state)
    (root : Occurrence roles) (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (bounds : List (GeneralNominalInspection.Bounds context.state)) (model : Assignment)
    (same : report (reobserve context next) declaration bounds =
      transferReport context next (report context declaration bounds))
    (valid : GeneralNominalState.Models (reobserve context next).state model)
    (old : GeneralNominalRecursiveCandidates.BranchModels registry context root declaration checked bounds model) :
    GeneralNominalRecursiveCandidates.BranchModels registry (reobserve context next)
      root declaration checked bounds model
```

```lean
theorem instance_of_reports (registry : Registry) (context : Context) (next : Observation context.state)
    (model : Assignment) (root : Occurrence roles) (key : Nat) (children : List (Occurrence roles))
    (same : PreservesAt registry context next root)
    (valid : GeneralNominalState.Models (reobserve context next).state model)
    (old : GeneralDictionaryRecursiveEvidence.Instance registry context model root key children) :
    GeneralDictionaryRecursiveEvidence.Instance registry (reobserve context next) model root key children
```

```lean
theorem node_of_reports (registry : Registry) (context : Context) (next : Observation context.state)
    (model : Assignment) (root : Occurrence roles) (key : Nat) (children : List (Occurrence roles))
    (dictionaries : List GeneralDictionaryReadback.Payload)
    (same : PreservesAt registry context next root)
    (valid : GeneralNominalState.Models (reobserve context next).state model)
    (old : GeneralDictionaryRecursiveEvidence.Instance registry context model root key children)
    (given : CommonRoleOutermostResolver.All₂
      (GeneralDictionaryRecursiveEvidence.Evidence registry (reobserve context next) model)
      children dictionaries) :
    GeneralDictionaryRecursiveEvidence.Evidence registry (reobserve context next) model root
      (.node key dictionaries)
```

```lean
theorem evidence_of_reports (registry : Registry) (context : Context) (next : Observation context.state)
    (model : Assignment) (root : Occurrence roles) (payload : GeneralDictionaryReadback.Payload)
    (same : ∀ occurrence : Occurrence roles, PreservesAt registry context next occurrence)
    (valid : GeneralNominalState.Models (reobserve context next).state model)
    (old : GeneralDictionaryRecursiveEvidence.Evidence registry context model root payload) :
    GeneralDictionaryRecursiveEvidence.Evidence registry (reobserve context next) model root payload
```

## GeneralDictionaryInspectionTransportExamples

```lean
theorem reobserve_eq : reobserve installed.context observation = refreshedContext
```

```lean
theorem parent_preserves : PreservesAt registry installed.context observation root
```

```lean
theorem current_parent_instance (m : Assignment) (valid : Models refreshed m) :
    GeneralDictionaryRecursiveEvidence.Instance registry refreshedContext m root 2 [child]
```

```lean
theorem nonvacuous_refreshed_parent :
    Models refreshed model ∧
      GeneralDictionaryRecursiveEvidence.Instance registry refreshedContext model root 2 [child]
```

```lean
theorem child_descriptor_changed :
    installed.context.state.nominals ⟨2,by decide +kernel⟩ = none ∧
    refreshedContext.state.nominals ⟨2,by decide +kernel⟩ =
      some GeneralNominalFeedbackRefresh.descriptor
```

## GeneralDictionaryRecordedRefresh

```lean
theorem recorded_refresh_instance (registry : Registry) (root : Occurrence roles)
    (before : State roles) (formed : GeneralNominalFeedbackSteps.SourceFormed registry root before)
    (packet : Packet roles) (recorded : packet ∈ before.packets)
    (growth : GeneralDictionaryOrdinaryTrace.Extension packet.context before.context)
    (next : Observation before.context.state)
    (refresh : GeneralNominalCycleSteps.Refresh before (reobserve before.context next))
    (same : PreservesAt registry before.context next packet.site.occurrence)
    (model : Assignment) (valid : Models (regenerate before (reobserve before.context next)) model) :
    GeneralDictionaryRecursiveEvidence.Instance registry (reobserve before.context next) model
      packet.site.occurrence packet.declaration.id packet.children
```

```lean
theorem recorded_refresh_tail_instance (registry : Registry) (root : Occurrence roles)
    (before after : State roles) (formed : GeneralNominalFeedbackSteps.SourceFormed registry root before)
    (packet : Packet roles) (recorded : packet ∈ before.packets)
    (growth : GeneralDictionaryOrdinaryTrace.Extension packet.context before.context)
    (next : Observation before.context.state)
    (refresh : GeneralNominalCycleSteps.Refresh before (reobserve before.context next))
    (same : PreservesAt registry before.context next packet.site.occurrence)
    (path : B4Target.Steps (GeneralDictionaryOrdinaryTrace.OrdinaryStep registry root)
      (regenerate before (reobserve before.context next)) after)
    (model : Assignment) (valid : Models after model) :
    GeneralDictionaryRecursiveEvidence.Instance registry after.context model
      packet.site.occurrence packet.declaration.id packet.children
```

```lean
theorem recorded_refresh_tail_evidence (registry : Registry) (root : Occurrence roles)
    (before after : State roles) (formed : GeneralNominalFeedbackSteps.SourceFormed registry root before)
    (packet : Packet roles) (recorded : packet ∈ before.packets)
    (growth : GeneralDictionaryOrdinaryTrace.Extension packet.context before.context)
    (next : Observation before.context.state)
    (refresh : GeneralNominalCycleSteps.Refresh before (reobserve before.context next))
    (same : PreservesAt registry before.context next packet.site.occurrence)
    (path : B4Target.Steps (GeneralDictionaryOrdinaryTrace.OrdinaryStep registry root)
      (regenerate before (reobserve before.context next)) after)
    (model : Assignment) (valid : Models after model) (dictionaries : List Payload)
    (given : CommonRoleOutermostResolver.All₂
      (GeneralDictionaryRecursiveEvidence.Evidence registry after.context model) packet.children dictionaries) :
    GeneralDictionaryRecursiveEvidence.Evidence registry after.context model packet.site.occurrence
      (.node packet.declaration.id dictionaries)
```

## GeneralDictionaryRefinementInspectionFacts

```lean
theorem none_of_visible (context : Context) (next : Observation context.state)
    (view : next.view = context.state.view) (slot : Fin context.state.base.slots)
    (visible : context.state.view.heads slot ≠ .deferred .unresolved) : next.nominals slot = none
```

```lean
theorem finished_append (first last : Report state) :
    Finished (first.append last) ↔ Finished first ∧ Finished last
```

```lean
theorem finished_visit (bounds : GeneralNominalInspection.Bounds state) (origin : Option Origin)
    (test : Test) (value : Report state) :
    Finished (Report.visit bounds origin test value) ↔ Finished value
```

```lean
theorem block_not_finished (bounds : GeneralNominalInspection.Bounds state) : ¬ Finished (block bounds)
```

## GeneralDictionaryRefreshDescriptors

```lean
theorem embed_identity (context : Context) (next : Observation context.state)
    (refinement : Refines context.state (reobserve context next).state) :
    refinement.base.embed = id
```

```lean
theorem rename_descriptor_identity (descriptor : GeneralNominalState.Descriptor slots) :
    renameDescriptor id descriptor = descriptor
```

```lean
theorem descriptor_preserved (context : Context) (next : Observation context.state)
    (refinement : Refines context.state (reobserve context next).state)
    (slot : Fin context.state.base.slots) (descriptor : GeneralNominalState.Descriptor context.state.base.slots)
    (recorded : context.state.nominals slot = some descriptor) :
    next.nominals slot = some descriptor
```

## GeneralDictionaryRefreshTrace

```lean
theorem step_feedback (registry : Registry) (root site : Occurrence roles)
    (before after : State roles) (step : Step registry root site before after) :
    GeneralNominalFeedbackSteps.Step registry root before after
```

```lean
theorem trace_feedback (registry : Registry) (root site : Occurrence roles)
    (before after : State roles) (path : B4Target.Steps (Step registry root site) before after) :
    B4Target.Steps (GeneralNominalFeedbackSteps.Step registry root) before after
```

```lean
theorem step_instance (registry : Registry) (root site : Occurrence roles)
    (before after : State roles) (step : Step registry root site before after)
    (model : Assignment) (valid : Models after model) (key : Nat) (children : List (Occurrence roles))
    (old : GeneralDictionaryRecursiveEvidence.Instance registry before.context model site key children) :
    GeneralDictionaryRecursiveEvidence.Instance registry after.context model site key children
```

```lean
theorem trace_instance (registry : Registry) (root site : Occurrence roles)
    (before after : State roles) (path : B4Target.Steps (Step registry root site) before after)
    (model : Assignment) (valid : Models after model) (key : Nat) (children : List (Occurrence roles))
    (old : GeneralDictionaryRecursiveEvidence.Instance registry before.context model site key children) :
    GeneralDictionaryRecursiveEvidence.Instance registry after.context model site key children
```

```lean
theorem recorded_trace_instance (registry : Registry) (root : Occurrence roles)
    (before after : State roles) (formed : GeneralNominalFeedbackSteps.SourceFormed registry root before)
    (packet : Packet roles) (recorded : packet ∈ before.packets)
    (growth : GeneralDictionaryOrdinaryTrace.Extension packet.context before.context)
    (path : B4Target.Steps (Step registry root packet.site.occurrence) before after)
    (model : Assignment) (valid : Models after model) :
    GeneralDictionaryRecursiveEvidence.Instance registry after.context model
      packet.site.occurrence packet.declaration.id packet.children
```

## GeneralDictionarySelectedLocality

```lean
theorem footprint_of_occupied (registry : Registry) (context : Context)
    (next : Observation context.state) (root : Occurrence roles) (key : Nat)
    (refinement : GeneralNominalRefinements.Refines context.state (reobserve context next).state)
    (occupied : OccupiedFor registry context root key) : FootprintFor registry context next root key
```

```lean
theorem instance_of_footprint (registry : Registry) (context : Context)
    (next : Observation context.state) (view : next.view = context.state.view)
    (model : Assignment) (root : Occurrence roles) (key : Nat) (children : List (Occurrence roles))
    (same : FootprintFor registry context next root key)
    (valid : GeneralNominalState.Models (reobserve context next).state model)
    (old : GeneralDictionaryRecursiveEvidence.Instance registry context model root key children) :
    GeneralDictionaryRecursiveEvidence.Instance registry (reobserve context next) model root key children
```

```lean
theorem instance_of_occupied (registry : Registry) (context : Context)
    (next : Observation context.state) (view : next.view = context.state.view)
    (refinement : GeneralNominalRefinements.Refines context.state (reobserve context next).state)
    (model : Assignment) (root : Occurrence roles) (key : Nat) (children : List (Occurrence roles))
    (occupied : OccupiedFor registry context root key)
    (valid : GeneralNominalState.Models (reobserve context next).state model)
    (old : GeneralDictionaryRecursiveEvidence.Instance registry context model root key children) :
    GeneralDictionaryRecursiveEvidence.Instance registry (reobserve context next) model root key children
```

```lean
theorem recorded_instance (registry : Registry) (root : Occurrence roles)
    (before : State roles) (formed : GeneralNominalFeedbackSteps.SourceFormed registry root before)
    (packet : Packet roles) (recorded : packet ∈ before.packets)
    (growth : GeneralDictionaryOrdinaryTrace.Extension packet.context before.context)
    (next : Observation before.context.state) (view : next.view = before.context.state.view)
    (refresh : GeneralNominalCycleSteps.Refresh before (reobserve before.context next))
    (occupied : OccupiedFor registry before.context packet.site.occurrence packet.declaration.id)
    (model : Assignment) (valid : Models (regenerate before (reobserve before.context next)) model) :
    GeneralDictionaryRecursiveEvidence.Instance registry (reobserve before.context next) model
      packet.site.occurrence packet.declaration.id packet.children
```

## GeneralDictionarySelectedLocalityExamples

```lean
theorem parent_occupied : OccupiedFor registry installed.context root 2
```

```lean
theorem recorded_parent_current (m : Assignment) (valid : Models refreshed m) :
    GeneralDictionaryRecursiveEvidence.Instance registry refreshedContext m root 2 [child]
```

```lean
theorem actual_nonvacuous_parent :
    Models refreshed model ∧
    GeneralDictionaryRecursiveEvidence.Instance registry refreshedContext model root 2 [child] ∧
    GeneralNominalFeedbackK2.Local registry refreshed child .rejected
```

## GeneralDictionarySelectedTree

```lean
theorem footprint_child (registry : Registry) (context : Context) (next : Observation context.state)
    (root : Occurrence roles) (key : Nat) (children : List (Dictionary roles))
    (same : FootprintTree registry context next (.node root key children))
    (child : Dictionary roles) (member : child ∈ children) : FootprintTree registry context next child
```

```lean
theorem indexed_of_footprint (registry : Registry) (context : Context) (next : Observation context.state)
    (view : next.view = context.state.view) (model : Assignment)
    (valid : GeneralNominalState.Models (reobserve context next).state model)
    (tree : Dictionary roles)
    (old : Evidence (GeneralDictionaryRecursiveEvidence.Instance registry context model) tree)
    (same : FootprintTree registry context next tree) :
    Evidence (GeneralDictionaryRecursiveEvidence.Instance registry (reobserve context next) model) tree
```

```lean
theorem erased_of_footprint (registry : Registry) (context : Context) (next : Observation context.state)
    (view : next.view = context.state.view) (model : Assignment)
    (valid : GeneralNominalState.Models (reobserve context next).state model)
    (root : Occurrence roles) (payload : GeneralDictionaryReadback.Payload) (tree : Dictionary roles)
    (readback : Readback root payload tree)
    (old : Evidence (GeneralDictionaryRecursiveEvidence.Instance registry context model) tree)
    (same : FootprintTree registry context next tree) :
    GeneralDictionaryRecursiveEvidence.Evidence registry (reobserve context next) model root payload
```

```lean
theorem indexed_of_occupied (registry : Registry) (context : Context) (next : Observation context.state)
    (view : next.view = context.state.view)
    (refinement : GeneralNominalRefinements.Refines context.state (reobserve context next).state)
    (model : Assignment) (valid : GeneralNominalState.Models (reobserve context next).state model)
    (tree : Dictionary roles)
    (old : Evidence (GeneralDictionaryRecursiveEvidence.Instance registry context model) tree)
    (occupied : ∀ occurrence key, (occurrence,key) ∈ observations tree → OccupiedFor registry context occurrence key) :
    Evidence (GeneralDictionaryRecursiveEvidence.Instance registry (reobserve context next) model) tree
```

```lean
theorem footprint_equivalent (registry : Registry) (context : Context) (next : Observation context.state)
    (first last : Dictionary roles) (equal : DictionaryEquivalent first last) :
    FootprintTree registry context next first ↔ FootprintTree registry context next last
```

## GeneralDictionaryTreeTransport

```lean
theorem child_observation (children : List (Dictionary roles)) (tree : Dictionary roles)
    (member : tree ∈ children) (entry : Occurrence roles × Nat)
    (present : entry ∈ observations tree) : entry ∈ childObservations children
```

```lean
theorem preserves_root (registry : Registry) (context : Context) (next : Observation context.state)
    (root : Occurrence roles) (key : Nat) (children : List (Dictionary roles))
    (same : PreservesTree registry context next (.node root key children)) :
    PreservesAt registry context next root
```

```lean
theorem preserves_child (registry : Registry) (context : Context) (next : Observation context.state)
    (root : Occurrence roles) (key : Nat) (children : List (Dictionary roles))
    (same : PreservesTree registry context next (.node root key children))
    (child : Dictionary roles) (member : child ∈ children) : PreservesTree registry context next child
```

```lean
theorem indexed_of_reports (registry : Registry) (context : Context) (next : Observation context.state)
    (model : Assignment) (valid : GeneralNominalState.Models (reobserve context next).state model)
    (tree : Dictionary roles)
    (old : Evidence (GeneralDictionaryRecursiveEvidence.Instance registry context model) tree)
    (same : PreservesTree registry context next tree) :
    Evidence (GeneralDictionaryRecursiveEvidence.Instance registry (reobserve context next) model) tree
```

```lean
theorem erased_of_witness_reports (registry : Registry) (context : Context) (next : Observation context.state)
    (model : Assignment) (valid : GeneralNominalState.Models (reobserve context next).state model)
    (root : Occurrence roles) (payload : GeneralDictionaryReadback.Payload) (tree : Dictionary roles)
    (readback : Readback root payload tree)
    (old : Evidence (GeneralDictionaryRecursiveEvidence.Instance registry context model) tree)
    (same : PreservesTree registry context next tree) :
    GeneralDictionaryRecursiveEvidence.Evidence registry (reobserve context next) model root payload
```

```lean
theorem preserves_equivalent (registry : Registry) (context : Context) (next : Observation context.state)
    (first last : Dictionary roles) (equal : DictionaryEquivalent first last) :
    PreservesTree registry context next first ↔ PreservesTree registry context next last
```
