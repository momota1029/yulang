# Cycle175 named theorem statements

Public source signature excerpts. Shared namespace opens and variable declarations are supplied by each module, so these excerpts alone are not standalone declarations. Fully elaborated types, including inferred implicit parameters, are in theorem-types.txt. Definitions/private/generated declarations are excluded from the theorem count. Read source and trust-zero logs for proofs.

## GeneralDictionaryAgreedCertifiedEvidence175

```lean
theorem endpoint_reachable (context : GeneralNominalCandidates.Context)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    B4TargetV5.Reachable (boundary defer gap) registry root state
```

```lean
theorem diagnostic_resolves
    (checked : (boundary defer gap).Checked registry)
    (passed : certifyTable registry = true)
    (reachable : B4TargetV5.Reachable (boundary defer gap) registry root state) :
    Resolves (B4TargetV3.Local (boundary defer gap).toSourceBoundary registry state) root
      (diagnostic defer gap registry state root)
```

```lean
theorem diagnostic_exact
    (checked : (boundary defer gap).Checked registry)
    (passed : certifyTable registry = true)
    (reachable : B4TargetV5.Reachable (boundary defer gap) registry root state)
    (tree : Tree) :
    diagnostic defer gap registry state root = tree ↔
      Resolves (B4TargetV3.Local (boundary defer gap).toSourceBoundary registry state) root tree
```

```lean
theorem completed_iff
    (checked : (boundary defer gap).Checked registry)
    (passed : certifyTable registry = true)
    (reachable : B4TargetV5.Reachable (boundary defer gap) registry root state)
    (result : CommonRoleOutermostResolver.Result) :
    B4TargetV3.Completed (diagnostic defer gap registry state root) result ↔
      B4TargetV3.Classify (boundary defer gap).toSourceBoundary registry state root result
```

```lean
theorem halted_completed_evidence
    (checked : (boundary defer gap).Checked registry)
    (passed : certifyTable registry = true)
    (context : GeneralNominalCandidates.Context)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (halted : ∀ after, ¬ GeneralNominalActualInspectionSteps.Step registry root state after)
    (policy : ∀ demand, defer = true ∨ ¬ gap registry state demand)
    (dictionary : Payload)
    (completed : B4TargetV3.Completed (diagnostic defer gap registry state root) (.selected dictionary))
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    Evidence registry state.current.context model root dictionary
```

## GeneralDictionaryAgreedCompactTable175

```lean
theorem tableOn_correct (registry : Registry) (nodes : List Nat)
    (covers : ∀ role ∈ roleNodes registry, role ∈ nodes)
    (fuel : Nat) (present : role ∈ roleNodes registry) :
    lookup (tableOn registry nodes fuel) role = computedHeight registry fuel role
```

```lean
theorem compactNodes_covers (present : role ∈ roleNodes registry) :
    role ∈ compactNodes registry
```

```lean
theorem compactHeight_correct (registry : Registry) (fuel : Nat)
    (present : role ∈ roleNodes registry) :
    lookup (compactHeight registry fuel) role = computedHeight registry fuel role
```

```lean
theorem checkCompact_eq (registry : Registry) (fuel : Nat) :
    checkCompact registry fuel = checkTable registry fuel
```

```lean
theorem certifyCompact_eq (registry : Registry) :
    certifyCompact registry = certifyTable registry
```

```lean
theorem certifyCompact_iff : certifyCompact registry = true ↔ ∃ rank, RoleStratified registry rank
```

```lean
theorem certifyCompact_reorders (order : GeneralRegistryReordering.Reorders first last) :
    certifyCompact first = certifyCompact last
```

```lean
theorem tableOn_length (registry : Registry) (nodes : List Nat) (fuel : Nat) :
    (tableOn registry nodes (fuel+1)).length = nodes.length
```

```lean
theorem compactHeight_length (registry : Registry) (fuel : Nat) :
    (compactHeight registry (fuel+1)).length = (compactNodes registry).length
```

## GeneralDictionaryAgreedCompletion175

```lean
theorem selected_instance_of_recorded
    (recorded : RecordedCurrent registry state)
    (policy : defer = true ∨ ¬ gap registry state focus)
    (stable : (boundary defer gap).Stable registry state focus)
    (selected : Local defer gap registry state focus (.selected key children))
    (model : Assignment) (valid : Models state.current model) :
    Instance registry state.current.context model focus key children
```

```lean
theorem selected_evidence_of_recorded
    (recorded : RecordedCurrent registry state)
    (policy : defer = true ∨ ¬ gap registry state focus)
    (stable : (boundary defer gap).Stable registry state focus)
    (selected : Local defer gap registry state focus (.selected key children))
    (model : Assignment) (valid : Models state.current model) (dictionaries : List Payload)
    (given : All₂ (Evidence registry state.current.context model) children dictionaries) :
    Evidence registry state.current.context model focus (.node key dictionaries)
```

```lean
theorem dictionary_evidence
      (recorded : RecordedCurrent registry state)
      (policy : ∀ demand, defer = true ∨ ¬ gap registry state demand)
      (rootStable : (boundary defer gap).Stable registry state root)
      (generatedStable : ∀ demand, Generated state.current root demand →
        (boundary defer gap).Stable registry state demand)
      (model : Assignment) (valid : Models state.current model)
      (dictionary : Payload) (focus : Occurrence roles)
      (reached : focus = root ∨ Generated state.current root focus)
      (derived : B4TargetV3.Classify (boundary defer gap).toSourceBoundary registry state focus
        (.selected dictionary)) : Evidence registry state.current.context model focus dictionary
```

```lean
theorem dictionaries_evidence
      (recorded : RecordedCurrent registry state)
      (policy : ∀ demand, defer = true ∨ ¬ gap registry state demand)
      (rootStable : (boundary defer gap).Stable registry state root)
      (generatedStable : ∀ demand, Generated state.current root demand →
        (boundary defer gap).Stable registry state demand)
      (model : Assignment) (valid : Models state.current model)
      (dictionaries : List Payload) (demands : List (Occurrence roles))
      (reached : ∀ child, child ∈ demands → child = root ∨ Generated state.current root child)
      (derived : All₂ (fun child dictionary =>
        B4TargetV3.Classify (boundary defer gap).toSourceBoundary registry state child (.selected dictionary))
        demands dictionaries) :
      All₂ (Evidence registry state.current.context model) demands dictionaries
```

```lean
theorem halted_dictionary_evidence
    (checked : (boundary defer gap).Checked registry)
    (context : GeneralNominalCandidates.Context)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (halted : ∀ after, ¬ GeneralNominalActualInspectionSteps.Step registry root state after)
    (policy : ∀ demand, defer = true ∨ ¬ gap registry state demand)
    (model : Assignment) (valid : Models state.current model) (dictionary : Payload)
    (derived : B4TargetV3.Classify (boundary defer gap).toSourceBoundary registry state root (.selected dictionary)) :
    Evidence registry state.current.context model root dictionary
```

```lean
theorem halted_pending_dictionary_evidence
    (checked : (boundary true gap).Checked registry)
    (context : GeneralNominalCandidates.Context)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (halted : ∀ after, ¬ GeneralNominalActualInspectionSteps.Step registry root state after)
    (model : Assignment) (valid : Models state.current model) (dictionary : Payload)
    (derived : B4TargetV3.Classify (boundary true gap).toSourceBoundary registry state root (.selected dictionary)) :
    Evidence registry state.current.context model root dictionary
```

## GeneralDictionaryAgreedFlexibleCompletion175

```lean
theorem halted_dictionary_evidence
    (checked : (boundary defer gap).Checked registry)
    (context : GeneralNominalCandidates.Context)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (halted : ∀ after, ¬ GeneralNominalActualInspectionSteps.Step registry root state after)
    (policy : ∀ demand, defer = true ∨ ¬ gap registry state demand)
    (model : Assignment) (valid : Models state.current model) (dictionary : Payload)
    (derived : B4TargetV3.Classify (boundary defer gap).toSourceBoundary registry state root (.selected dictionary)) :
    Evidence registry state.current.context model root dictionary
```

```lean
theorem halted_pending_dictionary_evidence
    (checked : (boundary true gap).Checked registry)
    (context : GeneralNominalCandidates.Context)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (halted : ∀ after, ¬ GeneralNominalActualInspectionSteps.Step registry root state after)
    (model : Assignment) (valid : Models state.current model) (dictionary : Payload)
    (derived : B4TargetV3.Classify (boundary true gap).toSourceBoundary registry state root (.selected dictionary)) :
    Evidence registry state.current.context model root dictionary
```

```lean
theorem halted_completed_evidence
    (checked : (boundary defer gap).Checked registry)
    (passed : GeneralDictionaryAgreedTable175.certifyTable registry = true)
    (context : GeneralNominalCandidates.Context)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (halted : ∀ after, ¬ GeneralNominalActualInspectionSteps.Step registry root state after)
    (policy : ∀ demand, defer = true ∨ ¬ gap registry state demand)
    (dictionary : Payload)
    (completed : B4TargetV3.Completed
      (GeneralDictionaryAgreedCertifiedEvidence175.diagnostic defer gap registry state root) (.selected dictionary))
    (model : Assignment) (valid : Models state.current model) :
    Evidence registry state.current.context model root dictionary
```

## GeneralDictionaryAgreedFlexibleTrace175

```lean
theorem at_actual (action : At registry before focus after) :
    GeneralNominalActualInspectionSteps.At registry before focus after
```

```lean
theorem step_actual (step : Step registry root before after) :
    GeneralNominalActualInspectionSteps.Step registry root before after
```

```lean
theorem steps_actual (path : B4Target.Steps (Step registry root) before after) :
    B4Target.Steps (GeneralNominalActualInspectionSteps.Step registry root) before after
```

```lean
theorem step_models (step : Step registry root before after) (model : Assignment)
    (valid : Models after.current model) : Models before.current model
```

```lean
theorem step_formed
    (formed : GeneralNominalActualInspectionSteps.SourceFormed registry root before)
    (step : Step registry root before after) :
    GeneralNominalActualInspectionSteps.SourceFormed registry root after
```

```lean
theorem at_instance (action : At registry before focus after)
    (model : Assignment) (valid : Models after.current model)
    (occurrence : Occurrence roles) (key : Nat) (children : List (Occurrence roles))
    (old : Instance registry before.current.context model occurrence key children) :
    Instance registry after.current.context model occurrence key children
```

```lean
theorem step_recorded
    (formed : GeneralNominalActualInspectionSteps.SourceFormed registry root before)
    (old : RecordedCurrent registry before) (step : Step registry root before after) :
    RecordedCurrent registry after
```

```lean
theorem initial_recorded (context : GeneralNominalCandidates.Context) :
    RecordedCurrent registry (initial context root)
```

```lean
theorem trace_formed_recorded
    (formed : GeneralNominalActualInspectionSteps.SourceFormed registry root before)
    (old : RecordedCurrent registry before)
    (path : B4Target.Steps (Step registry root) before after) :
    GeneralNominalActualInspectionSteps.SourceFormed registry root after ∧ RecordedCurrent registry after
```

```lean
theorem initial_trace_recorded (context : GeneralNominalCandidates.Context)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (path : B4Target.Steps (Step registry root) (initial context root) after) :
    RecordedCurrent registry after
```

```lean
theorem initial_trace_instance (context : GeneralNominalCandidates.Context)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (path : B4Target.Steps (Step registry root) (initial context root) after)
    (packet : Packet roles) (member : packet ∈ after.current.packets)
    (model : Assignment) (valid : Models after.current model) :
    Instance registry after.current.context model packet.site.occurrence packet.declaration.id packet.children
```

```lean
theorem initial_trace_evidence (context : GeneralNominalCandidates.Context)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (path : B4Target.Steps (Step registry root) (initial context root) after)
    (packet : Packet roles) (member : packet ∈ after.current.packets)
    (model : Assignment) (valid : Models after.current model) (dictionaries : List Payload)
    (given : All₂ (Evidence registry after.current.context model) packet.children dictionaries) :
    Evidence registry after.current.context model packet.site.occurrence (.node packet.declaration.id dictionaries)
```

```lean
theorem old_at (action : GeneralDictionaryAgreedRefiningTrace174.At registry before focus after) :
    At registry before focus after
```

```lean
theorem old_step (step : GeneralDictionaryAgreedRefiningTrace174.Step registry root before after) :
    Step registry root before after
```

```lean
theorem old_steps (path : B4Target.Steps (GeneralDictionaryAgreedRefiningTrace174.Step registry root) before after) :
    B4Target.Steps (Step registry root) before after
```

## GeneralDictionaryAgreedTable175

```lean
theorem lookup_map (nodes : List Nat) (f : Nat → Nat) (present : role ∈ nodes) :
    lookup (nodes.map fun key => (key,f key)) role = f role
```

```lean
theorem parent_mem_nodes (visible : declaration ∈ registry.declarations) :
    declaration.role ∈ roleNodes registry
```

```lean
theorem childRoles_mem_nodes (present : child ∈ childRoles registry role) :
    child ∈ roleNodes registry
```

```lean
theorem heightTable_correct (registry : Registry) (fuel : Nat)
    (present : role ∈ roleNodes registry) :
    lookup (heightTable registry fuel) role = computedHeight registry fuel role
```

```lean
theorem checkTable_eq (registry : Registry) (fuel : Nat) :
    checkTable registry fuel = check registry fuel
```

```lean
theorem certifyTable_eq (registry : Registry) : certifyTable registry = certify registry
```

```lean
theorem certifyTable_iff : certifyTable registry = true ↔ ∃ rank, RoleStratified registry rank
```

```lean
theorem certifyTable_reorders (order : GeneralRegistryReordering.Reorders first last) :
    certifyTable first = certifyTable last
```

```lean
theorem wrap_certified : certifyTable GeneralDictionaryAgreedRoleExamples174.wrapOnly = true
```

```lean
theorem recursive_not_certified : certifyTable GeneralDeclarationExamples.registry = false
```

## GeneralDictionaryAgreedTableExamples175

```lean
theorem empty_all_fuel (fuel : Nat) : checkTable emptyGraph fuel = true
```

```lean
theorem empty_certified : certifyTable emptyGraph = true
```

```lean
theorem repeated_certified : certifyTable repeatedDAG = true
```

```lean
theorem repeated_zero_fails : checkTable repeatedDAG 0 = false
```

```lean
theorem repeated_one_passes : checkTable repeatedDAG 1 = true
```

```lean
theorem disconnected_all_fuel (fuel : Nat) : checkTable disconnectedCycle fuel = false
```

```lean
theorem disconnected_not_certified : certifyTable disconnectedCycle = false
```

```lean
theorem reverseGraph_reorders (source : Registry) :
    GeneralRegistryReordering.Reorders source (reverseGraph source)
```

```lean
theorem reverseGraph_certificate (source : Registry) :
    certifyTable source = certifyTable (reverseGraph source)
```

```lean
theorem reversed_cycle_not_certified : certifyTable (reverseGraph disconnectedCycle) = false
```

## GeneralDictionaryNominalOnlyRefresh175

```lean
theorem inspect_finished (context : Context) (next : Observation context.state)
    (refinement : GeneralNominalRefinements.Refines context.state (reobserve context next).state)
    (query : Query) (bounds : Bounds context.state) (origin : Option Origin)
    (allowed : NominalOnly query)
    (finished : Finished (inspect context.state query bounds origin)) :
    inspect (reobserve context next).state query bounds origin =
      transferReport context next (inspect context.state query bounds origin)
```

```lean
theorem inspectMany_finished (context : Context) (next : Observation context.state)
    (refinement : GeneralNominalRefinements.Refines context.state (reobserve context next).state)
    (queries : List Query) (bounds : List (Bounds context.state)) (origins : Nat → Option Origin) (index : Nat)
    (allowed : ∀ query ∈ queries, NominalOnly query)
    (finished : Finished (inspectMany context.state queries bounds origins index)) :
    inspectMany (reobserve context next).state queries bounds origins index =
      transferReport context next (inspectMany context.state queries bounds origins index)
```

```lean
theorem report_finished (context : Context) (next : Observation context.state)
    (refinement : GeneralNominalRefinements.Refines context.state (reobserve context next).state)
    (declaration : GeneralDeclarations.Declaration) (bounds : List (Bounds context.state))
    (allowed : DeclarationFragment context declaration)
    (finished : Finished (GeneralNominalRecursiveCandidates.report context declaration bounds)) :
    GeneralNominalRecursiveCandidates.report (reobserve context next) declaration bounds =
      transferReport context next (GeneralNominalRecursiveCandidates.report context declaration bounds)
```

```lean
theorem instance_refinement (registry : GeneralDeclarations.Registry)
    (context : Context) (next : Observation context.state)
    (refinement : GeneralNominalRefinements.Refines context.state (reobserve context next).state)
    (allowed : ∀ declaration ∈ registry.declarations, DeclarationFragment context declaration)
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models (reobserve context next).state model)
    (root : GeneralSourceDictionaries.Occurrence roles) (key : Nat)
    (children : List (GeneralSourceDictionaries.Occurrence roles))
    (old : GeneralDictionaryRecursiveEvidence.Instance registry context model root key children) :
    GeneralDictionaryRecursiveEvidence.Instance registry (reobserve context next) model root key children
```

```lean
theorem evidence_refinement (registry : GeneralDeclarations.Registry)
    (context : Context) (next : Observation context.state)
    (refinement : GeneralNominalRefinements.Refines context.state (reobserve context next).state)
    (allowed : ∀ declaration ∈ registry.declarations, DeclarationFragment context declaration)
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models (reobserve context next).state model)
    (root : GeneralSourceDictionaries.Occurrence roles) (payload : GeneralDictionaryReadback.Payload)
    (old : GeneralDictionaryRecursiveEvidence.Evidence registry context model root payload) :
    GeneralDictionaryRecursiveEvidence.Evidence registry (reobserve context next) model root payload
```

## GeneralDictionaryNominalViewRegression175

```lean
theorem view_changes : next.view ≠ before.state.view
```

```lean
theorem query_allowed : NominalOnly query
```

```lean
theorem finished_before : Finished (inspect before.state query (0,0) none)
```

```lean
theorem report_preserved : inspect after.state query (0,0) none =
    transferReport before next (inspect before.state query (0,0) none)
```

```lean
theorem finished_after : Finished (inspect after.state query (0,0) none)
```

```lean
theorem capture_before : bindings before.state (inspect before.state query (0,0) none) = [(0,(1,1))]
```

```lean
theorem capture_after : bindings after.state (inspect after.state query (0,0) none) = [(0,(1,1))]
```

```lean
theorem known_progress : ¬ GeneralNominalState.Known before.state 1 ∧
    GeneralNominalState.Known after.state 1
```

```lean
theorem models_nonempty : GeneralNominalState.Models before.state GeneralNominalExamples.model ∧
    GeneralNominalState.Models after.state GeneralNominalExamples.model
```
