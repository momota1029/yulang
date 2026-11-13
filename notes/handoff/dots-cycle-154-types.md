# Cycle 154 theorem statements

The exact signatures retain all explicit quantifiers and premises. Implicit variables and namespace openings are as in each linked source module. All results are soundness/supporting results, not general completeness or principality.

## GeneralDictionaryHistoricalRequestModels

[Source](../../lean/Yulang/GeneralDictionaryHistoricalRequestModels.lean)

### generated_eq

Side: soundness / auxiliary.

```lean
theorem generated_eq (before after : GeneralNominalCandidates.Context)
    (constructors : after.state.constructors = before.state.constructors)
    (interpretation : after.interpretation = before.interpretation)
    (requests : List Request) :
    generated after.state after.interpretation requests =
      generated before.state before.interpretation requests
```

### extension_generated

Side: soundness / auxiliary.

```lean
theorem extension_generated (before after : GeneralNominalCandidates.Context)
    (growth : GeneralDictionaryOrdinaryTrace.Extension before after) (requests : List Request) :
    generated after.state after.interpretation requests =
      generated before.state before.interpretation requests
```

### at_generated

Side: soundness / auxiliary.

```lean
theorem at_generated {roles : Roles.RoleDecls} (registry : Registry)
    (before after : State roles) (focus : Occurrence roles)
    (step : GeneralNominalFeedbackSteps.At registry before focus after) (requests : List Request) :
    generated after.context.state after.context.interpretation requests =
      generated before.context.state before.context.interpretation requests
```

### trace_generated

Side: soundness / auxiliary.

```lean
theorem trace_generated {roles : Roles.RoleDecls} (registry : Registry)
    (root : Occurrence roles) (before after : State roles)
    (path : B4Target.Steps (GeneralNominalFeedbackSteps.Step registry root) before after)
    (requests : List Request) :
    generated after.context.state after.context.interpretation requests =
      generated before.context.state before.context.interpretation requests
```

### generated_models_after_trace

Side: soundness / auxiliary.

```lean
theorem generated_models_after_trace {roles : Roles.RoleDecls} (registry : Registry)
    (root : Occurrence roles) (before after : State roles)
    (path : B4Target.Steps (GeneralNominalFeedbackSteps.Step registry root) before after)
    (requests : List Request)
    (observed : Observed before.context.state before.context.interpretation requests)
    (declaration : Declaration) (capture : GeneralDeclarationDemands.Capture)
    (report : GeneralNominalRecursiveInspection.Report after.context.state)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models after model) :
    GeneralNominalMaterialization.Models after.context.state declaration capture report
      (generated after.context.state after.context.interpretation requests) model
```

### generated_shape_after_trace

Side: soundness / auxiliary.

```lean
theorem generated_shape_after_trace {roles : Roles.RoleDecls} (registry : Registry)
    (root : Occurrence roles) (before after : State roles)
    (path : B4Target.Steps (GeneralNominalFeedbackSteps.Step registry root) before after)
    (requests : List Request)
    (observed : Observed before.context.state before.context.interpretation requests) :
    (generated after.context.state after.context.interpretation requests).variables = [] ∧
      (generated after.context.state after.context.interpretation requests).unknown = false
```

### actual_requests_models_after_trace

Side: soundness / auxiliary.

```lean
theorem actual_requests_models_after_trace {roles : Roles.RoleDecls} (registry : Registry)
    (root : Occurrence roles) (before after : State roles)
    (path : B4Target.Steps (GeneralNominalFeedbackSteps.Step registry root) before after)
    (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (captures : GeneralNominalAllocation.Bindings)
    (variables : GeneralDictionaryVariableRequirements.VariableClauses declaration)
    (observed : Observed before.context.state before.context.interpretation (rootRequests declaration root))
    (capture : GeneralDeclarationDemands.Capture)
    (report : GeneralNominalRecursiveInspection.Report after.context.state)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models after model) :
    GeneralNominalMaterialization.Models after.context.state declaration capture report
      (generated after.context.state after.context.interpretation
        (requests after.context.state registry root declaration checked captures)) model
```


## GeneralDictionaryValueEvidence

[Source](../../lean/Yulang/GeneralDictionaryValueEvidence.lean)

### stable_site

Side: soundness / auxiliary.

```lean
theorem stable_site (registry : Registry) (state : Tracked roles) (root : Occurrence roles)
    (stable : GeneralNominalValueSteps.Stable registry state root)
    (linked : GeneralNominalState.Linked state.current.context.state root.demand) :
    ∃ site ∈ state.current.sites, site.occurrence = root
```

### selected_support

Side: soundness / auxiliary.

```lean
theorem selected_support (registry : Registry) (state : Tracked roles) (root : Occurrence roles)
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalValueBoundary.Local registry state root (.selected key children)) :
    ∃ support, GeneralNominalValueSupport.DecisionGuard registry state root support
```

### stable_joint_packet

Side: soundness / auxiliary.

```lean
theorem stable_joint_packet (registry : Registry) (state : Tracked roles)
    (root : Occurrence roles) (key : Nat) (children : List (Occurrence roles))
    (stable : GeneralNominalValueSteps.Stable registry state root)
    (selected : GeneralNominalValueBoundary.Local registry state root (.selected key children))
    (joint : GeneralNominalJointCandidates.Joint registry state.current root key)
    (merges : ∀ site ∈ state.current.sites, site.occurrence = root →
      GeneralNominalFeedbackSteps.MergesClosed state.current site) :
    ∃ packet : Packet roles, packet.registry = registry ∧ packet.context = state.current.context ∧
      packet.site.occurrence = root ∧ packet.declaration.id = key ∧ packet.children = children ∧
      GeneralNominalFeedbackSteps.Installable registry state.current packet ∧
      GeneralNominalFeedbackSteps.Committed state.current packet
```

### stable_joint_instance

Side: soundness / auxiliary.

```lean
theorem stable_joint_instance (registry : Registry) (state : Tracked roles)
    (root : Occurrence roles) (key : Nat) (children : List (Occurrence roles))
    (stable : GeneralNominalValueSteps.Stable registry state root)
    (selected : GeneralNominalValueBoundary.Local registry state root (.selected key children))
    (joint : GeneralNominalJointCandidates.Joint registry state.current root key)
    (merges : ∀ site ∈ state.current.sites, site.occurrence = root →
      GeneralNominalFeedbackSteps.MergesClosed state.current site) :
    (∀ model, Models state.current model → Instance registry state.current.context model root key children) ∧
      ∀ child ∈ children, Generated state.current root child
```

### stable_joint_evidence

Side: soundness / auxiliary.

```lean
theorem stable_joint_evidence (registry : Registry) (state : Tracked roles)
    (root : Occurrence roles) (key : Nat) (children : List (Occurrence roles))
    (stable : GeneralNominalValueSteps.Stable registry state root)
    (selected : GeneralNominalValueBoundary.Local registry state root (.selected key children))
    (joint : GeneralNominalJointCandidates.Joint registry state.current root key)
    (merges : ∀ site ∈ state.current.sites, site.occurrence = root →
      GeneralNominalFeedbackSteps.MergesClosed state.current site)
    (model : Assignment) (valid : Models state.current model) (dictionaries : List Payload)
    (given : CommonRoleOutermostResolver.All₂
      (Evidence registry state.current.context model) children dictionaries) :
    Evidence registry state.current.context model root (.node key dictionaries)
```

### stable_merges_of_exact

Side: soundness / auxiliary.

```lean
theorem stable_merges_of_exact (registry : Registry) (state : Tracked roles) (root : Occurrence roles)
    (exact : GeneralNominalSupportSteps.Exact state)
    (stable : GeneralNominalValueSteps.Stable registry state root)
    (first last : GeneralNominalDemandMerging.Site roles)
    (one : first ∈ state.current.sites) (two : last ∈ state.current.sites)
    (reached : Generated state.current root first.occurrence)
    (same : GeneralNominalFeedbackSites.SameInputs state.current first last) :
    Alias state.current first.occurrence.identity last.occurrence.identity
```

### reachable_joint_instance

Side: soundness / auxiliary.

```lean
theorem reachable_joint_instance (registry : Registry) (state : Tracked roles)
    (root focus : Occurrence roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root state)
    (key : Nat) (children : List (Occurrence roles))
    (stable : GeneralNominalValueSteps.Stable registry state focus)
    (selected : GeneralNominalValueBoundary.Local registry state focus (.selected key children))
    (joint : GeneralNominalJointCandidates.Joint registry state.current focus key) :
    (∀ model, Models state.current model → Instance registry state.current.context model focus key children) ∧
      ∀ child ∈ children, Generated state.current focus child
```

### reachable_joint_evidence

Side: soundness / auxiliary.

```lean
theorem reachable_joint_evidence (registry : Registry) (state : Tracked roles)
    (root focus : Occurrence roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root state)
    (key : Nat) (children : List (Occurrence roles))
    (stable : GeneralNominalValueSteps.Stable registry state focus)
    (selected : GeneralNominalValueBoundary.Local registry state focus (.selected key children))
    (joint : GeneralNominalJointCandidates.Joint registry state.current focus key)
    (model : Assignment) (valid : Models state.current model) (dictionaries : List Payload)
    (given : CommonRoleOutermostResolver.All₂ (Evidence registry state.current.context model) children dictionaries) :
    Evidence registry state.current.context model focus (.node key dictionaries)
```

### steps_reobservation

Side: soundness / auxiliary.

```lean
theorem steps_reobservation (registry : Registry) (root : Occurrence roles)
    (before after : Tracked roles)
    (path : B4Target.Steps (GeneralNominalValueSteps.Step registry root) before after) :
    B4Target.Steps (GeneralNominalReobservationSteps.Step registry root)
      before.current after.current
```

### reachable_reobservation

Side: soundness / auxiliary.

```lean
theorem reachable_reobservation (registry : Registry) (root : Occurrence roles)
    (state : Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root state) :
    B4TargetV5.Reachable (GeneralNominalReobservationBoundary.boundary roles)
      registry root state.current
```

### reachable_packetFree_terminal

Side: soundness / auxiliary.

```lean
theorem reachable_packetFree_terminal (registry : Registry) (root focus : Occurrence roles)
    (state : Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root state)
    (empty : state.current.packets = [])
    (reached : focus = root ∨ Generated state.current root focus)
    (key : Nat) (children : List (Occurrence roles))
    (stable : GeneralNominalValueSteps.Stable registry state focus)
    (selected : GeneralNominalValueBoundary.Local registry state focus (.selected key children)) :
    children = [] ∧ ∀ model, Models state.current model →
      Evidence registry state.current.context model focus (.node key [])
```

### reachable_packetFree_evidence

Side: soundness / auxiliary.

```lean
theorem reachable_packetFree_evidence (registry : Registry) (root focus : Occurrence roles)
    (state : Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root state)
    (empty : state.current.packets = [])
    (reached : focus = root ∨ Generated state.current root focus)
    (key : Nat) (children : List (Occurrence roles))
    (stable : GeneralNominalValueSteps.Stable registry state focus)
    (selected : GeneralNominalValueBoundary.Local registry state focus (.selected key children))
    (model : Assignment) (valid : Models state.current model) (dictionaries : List Payload)
    (given : CommonRoleOutermostResolver.All₂
      (Evidence registry state.current.context model) children dictionaries) :
    Evidence registry state.current.context model focus (.node key dictionaries)
```


## GeneralDictionaryHistoricalTreeBranch

[Source](../../lean/Yulang/GeneralDictionaryHistoricalTreeBranch.lean)

### branch_models

Side: soundness / auxiliary.

```lean
theorem branch_models (registry : Registry) (saturationRoot root : Occurrence roles)
    (before after : GeneralNominalSaturationState.State roles)
    (path : B4Target.Steps (GeneralNominalReobservationSteps.Step registry saturationRoot) before after)
    (declaration : Declaration) (checked : DeclarationChecked registry.constructors roles declaration)
    (shape : Shape after.context registry root declaration checked)
    (observed : GeneralDictionaryObservedFiniteRequests.Observed before.context.state before.context.interpretation
      (GeneralNominalMaterialization.requests after.context.state registry root declaration checked
        (bindings after.context.state (report after.context declaration [(shape.slot,shape.slot)]))))
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalSaturationState.Models after model) :
    BranchModels registry after.context root declaration checked [(shape.slot,shape.slot)] model
```

### ready

Side: soundness / auxiliary.

```lean
theorem ready (registry : Registry) (saturationRoot root : Occurrence roles)
    (before after : GeneralNominalSaturationState.State roles)
    (path : B4Target.Steps (GeneralNominalReobservationSteps.Step registry saturationRoot) before after)
    (declaration : Declaration) (checked : DeclarationChecked registry.constructors roles declaration)
    (shape : Shape after.context registry root declaration checked)
    (observed : GeneralDictionaryObservedFiniteRequests.Observed before.context.state before.context.interpretation
      (GeneralNominalMaterialization.requests after.context.state registry root declaration checked
        (bindings after.context.state (report after.context declaration [(shape.slot,shape.slot)])))) :
    RequestReady registry after.context root declaration checked [(shape.slot,shape.slot)]
```

### instance_of_shape

Side: soundness / auxiliary.

```lean
theorem instance_of_shape (registry : Registry) (saturationRoot root : Occurrence roles)
    (before after : GeneralNominalSaturationState.State roles)
    (path : B4Target.Steps (GeneralNominalReobservationSteps.Step registry saturationRoot) before after)
    (declaration : Declaration) (visible : declaration ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (shape : Shape after.context registry root declaration checked)
    (observed : GeneralDictionaryObservedFiniteRequests.Observed before.context.state before.context.interpretation
      (GeneralNominalMaterialization.requests after.context.state registry root declaration checked
        (bindings after.context.state (report after.context declaration [(shape.slot,shape.slot)]))))
    (metadata : Metadata registry after.context)
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalSaturationState.Models after model) :
    Instance registry after.context model root declaration.id
      (GeneralNominalAllocation.children after.context.state registry root declaration checked
        (bindings after.context.state (report after.context declaration [(shape.slot,shape.slot)])))
```

### selected_instance

Side: soundness / auxiliary.

```lean
theorem selected_instance (registry : Registry) (saturationRoot root : Occurrence roles)
    (before after : GeneralNominalSaturationState.State roles)
    (path : B4Target.Steps (GeneralNominalReobservationSteps.Step registry saturationRoot) before after)
    (declaration : Declaration) (visible : declaration ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (shape : Shape after.context registry root declaration checked)
    (observed : GeneralDictionaryObservedFiniteRequests.Observed before.context.state before.context.interpretation
      (GeneralNominalMaterialization.requests after.context.state registry root declaration checked
        (bindings after.context.state (report after.context declaration [(shape.slot,shape.slot)]))))
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalFeedbackK2.Local registry after root (.selected key children))
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalSaturationState.Models after model) :
    declaration.id = key ∧ Instance registry after.context model root key children
```

### selected_branch

Side: soundness / auxiliary.

```lean
theorem selected_branch (registry : Registry) (saturationRoot root : Occurrence roles)
    (before after : GeneralNominalSaturationState.State roles)
    (path : B4Target.Steps (GeneralNominalReobservationSteps.Step registry saturationRoot) before after)
    (declaration : Declaration) (visible : declaration ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (shape : Shape after.context registry root declaration checked)
    (observed : GeneralDictionaryObservedFiniteRequests.Observed before.context.state before.context.interpretation
      (GeneralNominalMaterialization.requests after.context.state registry root declaration checked
        (bindings after.context.state (report after.context declaration [(shape.slot,shape.slot)]))))
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalFeedbackK2.Local registry after root (.selected key children))
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalSaturationState.Models after model) :
    declaration.id = key ∧ GeneralNominalJointCandidates.BranchAt registry after root declaration.id model
```

### value_selected_branch

Side: soundness / auxiliary.

```lean
theorem value_selected_branch (registry : Registry) (saturationRoot root : Occurrence roles)
    (before after : GeneralNominalSupport.Tracked roles)
    (path : B4Target.Steps (GeneralNominalValueSteps.Step registry saturationRoot) before after)
    (declaration : Declaration) (visible : declaration ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (shape : Shape after.current.context registry root declaration checked)
    (observed : GeneralDictionaryObservedFiniteRequests.Observed
      before.current.context.state before.current.context.interpretation
      (GeneralNominalMaterialization.requests after.current.context.state registry root declaration checked
        (bindings after.current.context.state (report after.current.context declaration [(shape.slot,shape.slot)]))))
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalValueBoundary.Local registry after root (.selected key children))
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalSaturationState.Models after.current model) :
    declaration.id = key ∧ GeneralNominalJointCandidates.BranchAt registry after.current root declaration.id model
```

### value_node_evidence

Side: soundness / auxiliary.

```lean
theorem value_node_evidence (registry : Registry) (saturationRoot root : Occurrence roles)
    (before after : GeneralNominalSupport.Tracked roles)
    (path : B4Target.Steps (GeneralNominalValueSteps.Step registry saturationRoot) before after)
    (declaration : Declaration) (visible : declaration ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (shape : Shape after.current.context registry root declaration checked)
    (observed : GeneralDictionaryObservedFiniteRequests.Observed
      before.current.context.state before.current.context.interpretation
      (GeneralNominalMaterialization.requests after.current.context.state registry root declaration checked
        (bindings after.current.context.state (report after.current.context declaration [(shape.slot,shape.slot)]))))
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalValueBoundary.Local registry after root (.selected key children))
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalSaturationState.Models after.current model)
    (dictionaries : List GeneralDictionaryReadback.Payload)
    (given : CommonRoleOutermostResolver.All₂
      (Evidence registry after.current.context model) children dictionaries) :
    Evidence registry after.current.context model root (.node key dictionaries)
```


## GeneralDictionaryHistoricalValueRequests

[Source](../../lean/Yulang/GeneralDictionaryHistoricalValueRequests.lean)

### at_generated

Side: soundness / auxiliary.

```lean
theorem at_generated {roles : Roles.RoleDecls} (registry : Registry)
    (before after : State roles) (focus : Occurrence roles)
    (step : GeneralNominalReobservationSteps.At registry before focus after)
    (requests : List Request) :
    generated after.context.state after.context.interpretation requests =
      generated before.context.state before.context.interpretation requests
```

### trace_generated

Side: soundness / auxiliary.

```lean
theorem trace_generated {roles : Roles.RoleDecls} (registry : Registry)
    (root : Occurrence roles) (before after : State roles)
    (path : B4Target.Steps (GeneralNominalReobservationSteps.Step registry root) before after)
    (requests : List Request) :
    generated after.context.state after.context.interpretation requests =
      generated before.context.state before.context.interpretation requests
```

### generated_models_after_trace

Side: soundness / auxiliary.

```lean
theorem generated_models_after_trace {roles : Roles.RoleDecls} (registry : Registry)
    (root : Occurrence roles) (before after : State roles)
    (path : B4Target.Steps (GeneralNominalReobservationSteps.Step registry root) before after)
    (requests : List Request)
    (observed : Observed before.context.state before.context.interpretation requests)
    (declaration : Declaration) (capture : GeneralDeclarationDemands.Capture)
    (report : GeneralNominalRecursiveInspection.Report after.context.state)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models after model) :
    GeneralNominalMaterialization.Models after.context.state declaration capture report
      (generated after.context.state after.context.interpretation requests) model
```

### generated_shape_after_trace

Side: soundness / auxiliary.

```lean
theorem generated_shape_after_trace {roles : Roles.RoleDecls} (registry : Registry)
    (root : Occurrence roles) (before after : State roles)
    (path : B4Target.Steps (GeneralNominalReobservationSteps.Step registry root) before after)
    (requests : List Request)
    (observed : Observed before.context.state before.context.interpretation requests) :
    (generated after.context.state after.context.interpretation requests).variables = [] ∧
      (generated after.context.state after.context.interpretation requests).unknown = false
```

### value_generated_models

Side: soundness / auxiliary.

```lean
theorem value_generated_models {roles : Roles.RoleDecls} (registry : Registry)
    (root : Occurrence roles) (before after : GeneralNominalSupport.Tracked roles)
    (path : B4Target.Steps (GeneralNominalValueSteps.Step registry root) before after)
    (requests : List Request)
    (observed : Observed before.current.context.state before.current.context.interpretation requests)
    (declaration : Declaration) (capture : GeneralDeclarationDemands.Capture)
    (report : GeneralNominalRecursiveInspection.Report after.current.context.state)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models after.current model) :
    GeneralNominalMaterialization.Models after.current.context.state declaration capture report
      (generated after.current.context.state after.current.context.interpretation requests) model
```

### value_generated_shape

Side: soundness / auxiliary.

```lean
theorem value_generated_shape {roles : Roles.RoleDecls} (registry : Registry)
    (root : Occurrence roles) (before after : GeneralNominalSupport.Tracked roles)
    (path : B4Target.Steps (GeneralNominalValueSteps.Step registry root) before after)
    (requests : List Request)
    (observed : Observed before.current.context.state before.current.context.interpretation requests) :
    (generated after.current.context.state after.current.context.interpretation requests).variables = [] ∧
      (generated after.current.context.state after.current.context.interpretation requests).unknown = false
```


## GeneralDictionaryRecordedRequestModels

[Source](../../lean/Yulang/GeneralDictionaryRecordedRequestModels.lean)

### subset_tests

Side: soundness / auxiliary.

```lean
theorem subset_tests (state : GeneralNominalState.State)
    (interpretation : GeneralNominalInspection.Interpretation) (small large : List Request)
    (included : ∀ request ∈ small, request ∈ large) :
    ∀ test ∈ (generated state interpretation small).tests,
      test ∈ (generated state interpretation large).tests
```

### coherent_at

Side: soundness / auxiliary.

```lean
theorem coherent_at (registry : Registry) (before after : State roles)
    (focus : Occurrence roles)
    (step : GeneralNominalReobservationSteps.At registry before focus after)
    (coherent : SchemaCoherent before) : SchemaCoherent after
```

### coherent_trace

Side: soundness / auxiliary.

```lean
theorem coherent_trace (registry : Registry) (root : Occurrence roles) (before after : State roles)
    (path : B4Target.Steps (GeneralNominalReobservationSteps.Step registry root) before after)
    (coherent : SchemaCoherent before) : SchemaCoherent after
```

### reachable_coherent

Side: soundness / auxiliary.

```lean
theorem reachable_coherent (registry : Registry) (root : Occurrence roles)
    (state : GeneralNominalSupport.Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root state) :
    SchemaCoherent state.current
```

### recorded_variableFree_models

Side: soundness / auxiliary.

```lean
theorem recorded_variableFree_models (state : State roles) (coherent : SchemaCoherent state)
    (packet : Packet roles) (member : packet ∈ state.packets) (batch : List Request)
    (included : ∀ request ∈ batch, request ∈ requests packet.context.state packet.registry
      packet.site.occurrence packet.declaration packet.checked packet.bindings)
    (closed : (generated packet.context.state packet.context.interpretation batch).variables = [])
    (declaration : Declaration) (capture : GeneralDeclarationDemands.Capture)
    (report : GeneralNominalRecursiveInspection.Report state.context.state)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model) :
    GeneralNominalMaterialization.Models state.context.state declaration capture report
      (generated state.context.state state.context.interpretation batch) model
```

### reachable_root_requests

Side: soundness / auxiliary.

```lean
theorem reachable_root_requests (registry : Registry) (root : Occurrence roles)
    (state : GeneralNominalSupport.Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root state)
    (packet : Packet roles) (member : packet ∈ state.current.packets)
    (closed : (generated packet.context.state packet.context.interpretation
      (rootRequests packet.declaration packet.site.occurrence)).variables = [])
    (declaration : Declaration) (capture : GeneralDeclarationDemands.Capture)
    (report : GeneralNominalRecursiveInspection.Report state.current.context.state)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    GeneralNominalMaterialization.Models state.current.context.state declaration capture report
      (generated state.current.context.state state.current.context.interpretation
        (rootRequests packet.declaration packet.site.occurrence)) model
```

### subset_known

Side: soundness / auxiliary.

```lean
theorem subset_known (state : GeneralNominalState.State)
    (interpretation : GeneralNominalInspection.Interpretation) (small large : List Request)
    (included : ∀ request ∈ small, request ∈ large)
    (known : (generated state interpretation large).unknown = false) :
    (generated state interpretation small).unknown = false
```

### requestsKnown_at

Side: soundness / auxiliary.

```lean
theorem requestsKnown_at (registry : Registry) (before after : State roles)
    (focus : Occurrence roles)
    (step : GeneralNominalReobservationSteps.At registry before focus after)
    (known : RequestsKnown before) : RequestsKnown after
```

### requestsKnown_trace

Side: soundness / auxiliary.

```lean
theorem requestsKnown_trace (registry : Registry) (root : Occurrence roles)
    (before after : State roles)
    (path : B4Target.Steps (GeneralNominalReobservationSteps.Step registry root) before after)
    (known : RequestsKnown before) : RequestsKnown after
```

### reachable_requestsKnown

Side: soundness / auxiliary.

```lean
theorem reachable_requestsKnown (registry : Registry) (root : Occurrence roles)
    (state : GeneralNominalSupport.Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root state) :
    RequestsKnown state.current
```

### reachable_subset_known

Side: soundness / auxiliary.

```lean
theorem reachable_subset_known (registry : Registry) (root : Occurrence roles)
    (state : GeneralNominalSupport.Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root state)
    (packet : Packet roles) (member : packet ∈ state.current.packets) (batch : List Request)
    (included : ∀ request ∈ batch, request ∈ requests packet.context.state packet.registry
      packet.site.occurrence packet.declaration packet.checked packet.bindings) :
    (generated state.current.context.state state.current.context.interpretation batch).unknown = false
```

### reachable_root_closed

Side: soundness / auxiliary.

```lean
theorem reachable_root_closed (registry : Registry) (root : Occurrence roles)
    (state : GeneralNominalSupport.Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root state)
    (packet : Packet roles) (member : packet ∈ state.current.packets)
    (closed : (generated packet.context.state packet.context.interpretation
      (rootRequests packet.declaration packet.site.occurrence)).variables = []) :
    (generated state.current.context.state state.current.context.interpretation
      (rootRequests packet.declaration packet.site.occurrence)).variables = [] ∧
    (generated state.current.context.state state.current.context.interpretation
      (rootRequests packet.declaration packet.site.occurrence)).unknown = false
```


## GeneralDictionaryFiniteObservedExample

[Source](../../lean/Yulang/GeneralDictionaryFiniteObservedExample.lean)

### state_models

Side: soundness / auxiliary.

```lean
theorem state_models : GeneralNominalState.Models state model
```

### translation

Side: soundness / auxiliary.

```lean
theorem translation : GeneralNominalInspection.translate state.constructors interpretation
    (GeneralDeclarationPatterns.normalize request.pattern) = query
```

### observed

Side: soundness / auxiliary.

```lean
theorem observed : Observed state interpretation [request]
```

### no_closed_tree

Side: soundness / auxiliary.

```lean
theorem no_closed_tree (slot : Fin state.base.slots) :
    ¬ Nonempty (GeneralDictionaryObservedClosedRequests.Tree state slot query)
```

### not_closed_observed

Side: soundness / auxiliary.

```lean
theorem not_closed_observed :
    ¬ GeneralDictionaryObservedClosedRequests.Observed state interpretation [request]
```

### tests_exact

Side: soundness / auxiliary.

```lean
theorem tests_exact : (generated state interpretation [request]).tests =
    [(.source 0,.nominal 0 3),
     (.nominal (.source 0) 0 0,.scalar .int),
     (.nominal (.source 0) 0 1,.scalar .int),
     (.nominal (.source 0) 0 2,.scalar .int)]
```

### every_source_model

Side: soundness / auxiliary.

```lean
theorem every_source_model (declaration : GeneralDeclarations.Declaration)
    (capture : GeneralDeclarationDemands.Capture) (report : GeneralNominalRecursiveInspection.Report state)
    (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models state assignment) :
    Models state declaration capture report (generated state interpretation [request]) assignment
```

### inhabited_request_models

Side: soundness / auxiliary.

```lean
theorem inhabited_request_models (declaration : GeneralDeclarations.Declaration)
    (capture : GeneralDeclarationDemands.Capture) (report : GeneralNominalRecursiveInspection.Report state) :
    GeneralNominalState.Models state model ∧
      Models state declaration capture report (generated state interpretation [request]) model
```

### checked

Side: soundness / auxiliary.

```lean
theorem checked : DeclarationChecked constructors roles declaration
```

### registry_checked

Side: soundness / auxiliary.

```lean
theorem registry_checked : Checked registry
```

### named_request_present

Side: soundness / auxiliary.

```lean
theorem named_request_present : root.demand.outputs ≠ []
```

### actual_requests_exact

Side: soundness / auxiliary.

```lean
theorem actual_requests_exact (captures : GeneralNominalAllocation.Bindings) :
    requests state registry root declaration checked captures = [request]
```

### actual_request_models

Side: soundness / auxiliary.

```lean
theorem actual_request_models (captures : GeneralNominalAllocation.Bindings)
    (capture : GeneralDeclarationDemands.Capture)
    (report : GeneralNominalRecursiveInspection.Report state)
    (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models state assignment) :
    Models state declaration capture report
      (generated state interpretation (requests state registry root declaration checked captures)) assignment
```

### metadata

Side: soundness / auxiliary.

```lean
theorem metadata : Metadata registry context
```

### initial_source

Side: soundness / auxiliary.

```lean
theorem initial_source : GeneralNominalSourceFormation.InitialSource registry context root where
  roles_agree
```

### report_exact

Side: soundness / auxiliary.

```lean
theorem report_exact : report context declaration [(1,1)] =
    { inspected
```

### branch_models

Side: soundness / auxiliary.

```lean
theorem branch_models (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models state assignment) :
    BranchModels registry context root declaration checked [(1,1)] assignment
```

### ready

Side: soundness / auxiliary.

```lean
theorem ready : RequestReady registry context root declaration checked [(1,1)]
```

### actual_instance

Side: soundness / auxiliary.

```lean
theorem actual_instance (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models state assignment) :
    Instance registry context assignment root declaration.id []
```

### full_evidence

Side: soundness / auxiliary.

```lean
theorem full_evidence (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models state assignment) :
    Evidence registry context assignment root (.node declaration.id [])
```

### actual_reachable

Side: soundness / auxiliary.

```lean
theorem actual_reachable :
    B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry root start
```

### reachable_inhabited_named_evidence

Side: soundness / auxiliary.

```lean
theorem reachable_inhabited_named_evidence :
    B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry root start ∧
    GeneralNominalSaturationState.Models start.current model ∧
    Evidence registry context model root (.node declaration.id []) ∧ root.demand.outputs ≠ []
```


## GeneralDictionaryFiniteObservedExampleClassify

[Source](../../lean/Yulang/GeneralDictionaryFiniteObservedExampleClassify.lean)

### no_root

Side: soundness / auxiliary.

```lean
theorem no_root : ¬ GeneralNominalFeedbackK2.RootK2 start.current root
```

### no_candidate

Side: soundness / auxiliary.

```lean
theorem no_candidate : ¬ GeneralNominalFeedbackK2.CandidateK2 registry start.current root
```

### root_ready

Side: soundness / auxiliary.

```lean
theorem root_ready : ¬ GeneralNominalState.RootPending state root.demand
```

### prepared

Side: soundness / auxiliary.

```lean
theorem prepared : Prepared registry context root declaration checked
```

### children_empty

Side: soundness / auxiliary.

```lean
theorem children_empty : GeneralNominalAllocation.children state registry root declaration checked
    (bindings state (report context declaration [(1,1)])) = []
```

### survivor

Side: soundness / auxiliary.

```lean
theorem survivor : Survivor registry context root declaration.id []
```

### unique

Side: soundness / auxiliary.

```lean
theorem unique : GeneralNominalLocalBoundary.Unique (GeneralNominalFeedbackK2.fields roles)
    registry start.current root declaration.id []
```

### selected

Side: soundness / auxiliary.

```lean
theorem selected : GeneralNominalFeedbackK2.Local registry start.current root
    (.selected declaration.id [])
```

### decisions

Side: soundness / auxiliary.

```lean
theorem decisions : DecisionGuard start registry root []
```

### support_selected

Side: soundness / auxiliary.

```lean
theorem support_selected : GeneralNominalSupportBoundary.Local registry start root
    (.selected declaration.id [])
```

### classified

Side: soundness / auxiliary.

```lean
theorem classified : B4TargetV3.Classify (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary
    registry start root (.selected (.node declaration.id []))
```

### stable_classified_named_dictionary

Side: soundness / auxiliary.

```lean
theorem stable_classified_named_dictionary :
    B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry root start ∧
    Models start.current model ∧ GeneralNominalSupportSteps.Stable registry start root ∧
    B4TargetV3.Classify (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary
      registry start root (.selected (.node declaration.id [])) ∧
    root.demand.outputs ≠ [] ∧
    ∀ assignment, Models start.current assignment →
      GeneralDictionaryRecursiveEvidence.Evidence registry context assignment root (.node declaration.id [])
```

### value_selected

Side: soundness / auxiliary.

```lean
theorem value_selected : GeneralNominalValueBoundary.Local registry start root
    (.selected declaration.id [])
```

### value_stable

Side: soundness / auxiliary.

```lean
theorem value_stable : GeneralNominalValueSteps.Stable registry start root
```

### value_reachable

Side: soundness / auxiliary.

```lean
theorem value_reachable :
    B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root start
```

### value_classified

Side: soundness / auxiliary.

```lean
theorem value_classified : B4TargetV3.Classify (GeneralNominalValueBoundary.boundary roles).toSourceBoundary
    registry start root (.selected (.node declaration.id []))
```

### value_stable_classified_named_dictionary

Side: soundness / auxiliary.

```lean
theorem value_stable_classified_named_dictionary :
    B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root start ∧
    Models start.current model ∧ GeneralNominalValueSteps.Stable registry start root ∧
    B4TargetV3.Classify (GeneralNominalValueBoundary.boundary roles).toSourceBoundary
      registry start root (.selected (.node declaration.id [])) ∧
    root.demand.outputs ≠ [] ∧
    ∀ assignment, Models start.current assignment →
      GeneralDictionaryRecursiveEvidence.Evidence registry context assignment root (.node declaration.id [])
```


## GeneralDictionaryFiniteObservedExampleNonterminal

[Source](../../lean/Yulang/GeneralDictionaryFiniteObservedExampleNonterminal.lean)

### source_models

Side: soundness / auxiliary.

```lean
theorem source_models : GeneralNominalState.Models source model
```

### checked

Side: soundness / auxiliary.

```lean
theorem checked : DeclarationChecked constructors roles declaration
```

### int_display_checked

Side: soundness / auxiliary.

```lean
theorem int_display_checked : GeneralDeclarations.DeclarationChecked constructors roles GeneralNominalExamples.intDisplay
```

### registry_checked

Side: soundness / auxiliary.

```lean
theorem registry_checked : Checked registry
```

### requests_exact

Side: soundness / auxiliary.

```lean
theorem requests_exact : GeneralNominalMaterialization.requests source registry root declaration checked
    (bindings source (report context declaration [(0,0)])) =
    [GeneralDictionaryFiniteObservedExample.request]
```

### metadata

Side: soundness / auxiliary.

```lean
theorem metadata : Metadata registry context
```

### named_request_present

Side: soundness / auxiliary.

```lean
theorem named_request_present : root.demand.outputs ≠ []
```

### nonterminal

Side: soundness / auxiliary.

```lean
theorem nonterminal : declaration.requirements ≠ []
```

### every_source_model

Side: soundness / auxiliary.

```lean
theorem every_source_model (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models source assignment) :
    BranchModels registry context root declaration checked [(0,0)] assignment
```

### actual_instance

Side: soundness / auxiliary.

```lean
theorem actual_instance : Instance registry context model root declaration.id
    (GeneralNominalAllocation.children source registry root declaration checked
      (bindings source (report context declaration [(0,0)])))
```

### initial_source

Side: soundness / auxiliary.

```lean
theorem initial_source : GeneralNominalSourceFormation.InitialSource registry context root where
  roles_agree
```

### initial_models

Side: soundness / auxiliary.

```lean
theorem initial_models : GeneralNominalSaturationState.Models start.current model
```

### actual_reachable

Side: soundness / auxiliary.

```lean
theorem actual_reachable :
    B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry root start
```

### root_ready

Side: soundness / auxiliary.

```lean
theorem root_ready : ¬ GeneralNominalState.RootPending source root.demand
```

### prepared

Side: soundness / auxiliary.

```lean
theorem prepared : Prepared registry context root declaration checked
```

### survivor

Side: soundness / auxiliary.

```lean
theorem survivor : Survivor registry context root declaration.id children
```

### initial_joint

Side: soundness / auxiliary.

```lean
theorem initial_joint : GeneralNominalJointCandidates.Joint registry start.current root declaration.id
```

### actual_children_count

Side: soundness / auxiliary.

```lean
theorem actual_children_count : children.length = 1
```


## GeneralDictionaryFiniteObservedExampleNonterminalClassification

[Source](../../lean/Yulang/GeneralDictionaryFiniteObservedExampleNonterminalClassification.lean)

### acyclic

Side: soundness / auxiliary.

```lean
theorem acyclic (source : Nat) : ¬ GeneralNominalFeedbackK2.Cycle installed.current source
```

### parent_selected

Side: soundness / auxiliary.

```lean
theorem parent_selected : GeneralNominalFeedbackK2.Local registry installed.current root (.selected declaration.id children)
```

### child_selected

Side: soundness / auxiliary.

```lean
theorem child_selected : GeneralNominalFeedbackK2.Local registry installed.current child (.selected intDisplay.id [])
```

### supported_parent

Side: soundness / auxiliary.

```lean
theorem supported_parent : GeneralNominalSupportBoundary.Local registry installed root (.selected declaration.id children)
```

### supported_child

Side: soundness / auxiliary.

```lean
theorem supported_child : GeneralNominalSupportBoundary.Local registry installed child (.selected intDisplay.id [])
```

### classified

Side: soundness / auxiliary.

```lean
theorem classified : B4TargetV3.Classify (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary
    registry installed root (.selected payload)
```

### stable_classified_named_dictionary

Side: soundness / auxiliary.

```lean
theorem stable_classified_named_dictionary :
    B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry root installed ∧
    Models installed.current model ∧ GeneralNominalSupportSteps.Stable registry installed root ∧
    B4TargetV3.Classify (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary registry installed root (.selected payload) ∧
    root.demand.outputs ≠ [] ∧ children.length = 1 ∧
    ∀ assignment, Models installed.current assignment → GeneralDictionaryRecursiveEvidence.Evidence registry current assignment root payload
```

### value_reachable

Side: soundness / auxiliary.

```lean
theorem value_reachable :
    B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root installed
```

### value_stable

Side: soundness / auxiliary.

```lean
theorem value_stable : GeneralNominalValueSteps.Stable registry installed root
```

### value_parent

Side: soundness / auxiliary.

```lean
theorem value_parent : GeneralNominalValueBoundary.Local registry installed root
    (.selected declaration.id children)
```

### value_child

Side: soundness / auxiliary.

```lean
theorem value_child : GeneralNominalValueBoundary.Local registry installed child
    (.selected intDisplay.id [])
```

### value_classified

Side: soundness / auxiliary.

```lean
theorem value_classified : B4TargetV3.Classify (GeneralNominalValueBoundary.boundary roles).toSourceBoundary
    registry installed root (.selected payload)
```

### value_installed_stable_classified_dictionary

Side: soundness / auxiliary.

```lean
theorem value_installed_stable_classified_dictionary :
    GeneralNominalValueSteps.Step registry root start installed ∧
    B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root installed ∧
    Models installed.current model ∧ GeneralNominalValueSteps.Stable registry installed root ∧
    B4TargetV3.Classify (GeneralNominalValueBoundary.boundary roles).toSourceBoundary
      registry installed root (.selected payload) ∧
    installed.current.packets ≠ [] ∧ root.demand.outputs ≠ [] ∧ children.length = 1 ∧
    ∀ assignment, Models installed.current assignment → GeneralDictionaryRecursiveEvidence.Evidence registry current assignment root payload
```


## GeneralDictionaryFiniteObservedExampleNonterminalClosure

[Source](../../lean/Yulang/GeneralDictionaryFiniteObservedExampleNonterminalClosure.lean)

### final_parent_instance

Side: soundness / auxiliary.

```lean
theorem final_parent_instance (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : Models installed.current assignment) :
    Instance registry current assignment root declaration.id children
```

### final_child_instance

Side: soundness / auxiliary.

```lean
theorem final_child_instance (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : Models installed.current assignment) :
    Instance registry current assignment child intDisplay.id []
```

### edges_exact

Side: soundness / auxiliary.

```lean
theorem edges_exact : installed.current.edges = [(root,child)]
```

### sites_exact

Side: soundness / auxiliary.

```lean
theorem sites_exact : installed.current.sites =
    [GeneralNominalDemandMerging.pointSite root,GeneralNominalFeedbackSites.childSite packet child]
```

### generated_cases

Side: soundness / auxiliary.

```lean
theorem generated_cases (focus : GeneralSourceDictionaries.Occurrence roles)
    (generated : Generated installed.current root focus) : focus = root ∨ focus = child
```

### merges_closed

Side: soundness / auxiliary.

```lean
theorem merges_closed (first last : GeneralNominalDemandMerging.Site roles)
    (one : first ∈ installed.current.sites) (two : last ∈ installed.current.sites)
    (same : GeneralNominalFeedbackSites.SameInputs installed.current first last) :
    Alias installed.current first.occurrence.identity last.occurrence.identity
```

### varying_model

Side: soundness / auxiliary.

```lean
theorem varying_model (name : Nat) (large : 2 ≤ name) : Models installed.current (varying name)
```

### refresh_large_unknown

Side: soundness / auxiliary.

```lean
theorem refresh_large_unknown (next : GeneralNominalCandidates.Context)
    (certificate : GeneralNominalCycleSteps.Refresh installed.current next) (id : Nat) (large : 2 ≤ id) :
    ¬ GeneralNominalState.Known next.state id
```

### context_complete

Side: soundness / auxiliary.

```lean
theorem context_complete : ContextComplete installed.current
```

### point_closed

Side: soundness / auxiliary.

```lean
theorem point_closed : GeneralNominalReobservationSteps.PointClosed current.state
```


## GeneralDictionaryFiniteObservedExampleNonterminalEvidence

[Source](../../lean/Yulang/GeneralDictionaryFiniteObservedExampleNonterminalEvidence.lean)

### children_exact

Side: soundness / auxiliary.

```lean
theorem children_exact : children = [child]
```

### child_arguments

Side: soundness / auxiliary.

```lean
theorem child_arguments : arguments context child = some [(1,1)]
```

### child_instance

Side: soundness / auxiliary.

```lean
theorem child_instance (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models source assignment) :
    Instance registry context assignment child intDisplay.id []
```

### child_evidence

Side: soundness / auxiliary.

```lean
theorem child_evidence (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models source assignment) :
    Evidence registry context assignment child (.node intDisplay.id [])
```

### full_evidence

Side: soundness / auxiliary.

```lean
theorem full_evidence (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models source assignment) : Evidence registry context assignment root payload
```

### reachable_inhabited_full_evidence

Side: soundness / auxiliary.

```lean
theorem reachable_inhabited_full_evidence :
    B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry root start ∧
    GeneralNominalSaturationState.Models start.current model ∧
    Evidence registry context model root payload ∧ root.demand.outputs ≠ [] ∧ children.length = 1
```


## GeneralDictionaryFiniteObservedExampleNonterminalFinalEvidence

[Source](../../lean/Yulang/GeneralDictionaryFiniteObservedExampleNonterminalFinalEvidence.lean)

### models_of_source

Side: soundness / auxiliary.

```lean
theorem models_of_source (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models source assignment) : Models installed.current assignment
```

### source_of_models

Side: soundness / auxiliary.

```lean
theorem source_of_models (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : Models installed.current assignment) : GeneralNominalState.Models source assignment
```

### installed_models_iff

Side: soundness / auxiliary.

```lean
theorem installed_models_iff (assignment : GeneralNominalCommonBridge.Assignment) :
    Models installed.current assignment ↔ GeneralNominalState.Models source assignment
```

### final_evidence

Side: soundness / auxiliary.

```lean
theorem final_evidence (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : Models installed.current assignment) :
    Evidence registry installed.current.context assignment root payload
```

### nonempty_journal

Side: soundness / auxiliary.

```lean
theorem nonempty_journal : installed.current.packets ≠ []
```

### reachable_full_named_dictionary

Side: soundness / auxiliary.

```lean
theorem reachable_full_named_dictionary :
    B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry root installed ∧
    Models installed.current model ∧ Evidence registry installed.current.context model root payload ∧
    installed.current.packets ≠ [] ∧ root.demand.outputs ≠ [] ∧ children.length = 1
```


## GeneralDictionaryFiniteObservedExampleNonterminalInstallation

[Source](../../lean/Yulang/GeneralDictionaryFiniteObservedExampleNonterminalInstallation.lean)

### packet_children

Side: soundness / auxiliary.

```lean
theorem packet_children : packet.children = children
```

### enabled

Side: soundness / auxiliary.

```lean
theorem enabled : GeneralNominalFeedbackSteps.Installable registry start.current packet
```

### children_nonempty

Side: soundness / auxiliary.

```lean
theorem children_nonempty : children ≠ []
```

### novel

Side: soundness / auxiliary.

```lean
theorem novel : ¬ GeneralNominalFeedbackSteps.Committed start.current packet
```

### guard

Side: soundness / auxiliary.

```lean
theorem guard : GeneralNominalSupportSteps.PacketGuard start packet []
```

### install_at

Side: soundness / auxiliary.

```lean
theorem install_at : GeneralNominalSupportSteps.At registry start root installed
```

### install_step

Side: soundness / auxiliary.

```lean
theorem install_step : GeneralNominalSupportSteps.Step registry root start installed
```

### not_stable

Side: soundness / auxiliary.

```lean
theorem not_stable : ¬ GeneralNominalSupportSteps.Stable registry start root
```

### installed_reachable

Side: soundness / auxiliary.

```lean
theorem installed_reachable :
    B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry root installed
```

### value_install_step

Side: soundness / auxiliary.

```lean
theorem value_install_step : GeneralNominalValueSteps.Step registry root start installed
```


## GeneralDictionaryFiniteObservedExampleNonterminalSelected

[Source](../../lean/Yulang/GeneralDictionaryFiniteObservedExampleNonterminalSelected.lean)

### observation_decreases

Side: soundness / auxiliary.

```lean
theorem observation_decreases (first last name index : Nat) (actual : Ty)
    (observed : GeneralNominalProjections.Observes model (.argument (.source first) name index) (.inl actual))
    (same : Equivalent actual (model last).1) : height last < height first
```

### no_root

Side: soundness / auxiliary.

```lean
theorem no_root : ¬ GeneralNominalFeedbackK2.RootK2 start.current root
```

### no_candidate

Side: soundness / auxiliary.

```lean
theorem no_candidate :
    ¬ GeneralNominalFeedbackK2.CandidateK2 registry start.current root
```

### unique

Side: soundness / auxiliary.

```lean
theorem unique : GeneralNominalLocalBoundary.Unique (GeneralNominalFeedbackK2.fields roles)
    registry start.current root declaration.id children
```

### selected

Side: soundness / auxiliary.

```lean
theorem selected : GeneralNominalFeedbackK2.Local registry start.current root
    (.selected declaration.id children)
```

### decisions

Side: soundness / auxiliary.

```lean
theorem decisions : DecisionGuard start registry root []
```

### support_selected

Side: soundness / auxiliary.

```lean
theorem support_selected : GeneralNominalSupportBoundary.Local registry start root
    (.selected declaration.id children)
```


## GeneralDictionaryFiniteObservedExampleNonterminalStable

[Source](../../lean/Yulang/GeneralDictionaryFiniteObservedExampleNonterminalStable.lean)

### installs_committed

Side: soundness / auxiliary.

```lean
theorem installs_committed (p : Packet roles)
    (reached : Generated installed.current root p.site.occurrence)
    (enabled : GeneralNominalFeedbackSteps.Installable registry installed.current p) :
    GeneralNominalFeedbackSteps.Committed installed.current p
```

### feedback_stable

Side: soundness / auxiliary.

```lean
theorem feedback_stable : GeneralNominalFeedbackSteps.Stable registry installed.current root
```

### stable

Side: soundness / auxiliary.

```lean
theorem stable : GeneralNominalSupportSteps.Stable registry installed root
```

### stable_reachable_named_dictionary

Side: soundness / auxiliary.

```lean
theorem stable_reachable_named_dictionary :
    B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry root installed ∧
    Models installed.current model ∧ GeneralNominalSupportSteps.Stable registry installed root ∧
    root.demand.outputs ≠ [] ∧ children.length = 1 ∧
    ∀ assignment, Models installed.current assignment → Evidence registry current assignment root payload
```


## GeneralDictionaryFiniteObservedExampleReserved

[Source](../../lean/Yulang/GeneralDictionaryFiniteObservedExampleReserved.lean)

### reserved_source

Side: soundness / auxiliary.

```lean
theorem reserved_source : 2 ∈ GeneralNominalState.sources state
```

### no_target_slot

Side: soundness / auxiliary.

```lean
theorem no_target_slot : ¬ ∃ slot : Fin state.base.slots, state.base.source slot = 2
```

### not_observed

Side: soundness / auxiliary.

```lean
theorem not_observed : ¬ GeneralDictionaryObservedFiniteRequests.Observed state interpretation [request]
```

### source_models

Side: soundness / auxiliary.

```lean
theorem source_models : GeneralNominalState.Models state model
```

### actual_requests_exact

Side: soundness / auxiliary.

```lean
theorem actual_requests_exact (captures : GeneralNominalAllocation.Bindings) :
    requests state registry root declaration checked captures = [request]
```

### initial_source

Side: soundness / auxiliary.

```lean
theorem initial_source : GeneralNominalSourceFormation.InitialSource registry context root where
  roles_agree
```

### initial_reachable

Side: soundness / auxiliary.

```lean
theorem initial_reachable :
    B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry root start
```

### tests_exact

Side: soundness / auxiliary.

```lean
theorem tests_exact : (generated state interpretation [request]).tests =
    [(.source 2,.nominal 0 3),
     (.nominal (.source 2) 0 0,.scalar .int),
     (.nominal (.source 2) 0 1,.scalar .int),
     (.nominal (.source 2) 0 2,.scalar .int)]
```

### initial_countermodel

Side: soundness / auxiliary.

```lean
theorem initial_countermodel (capture : GeneralDeclarationDemands.Capture)
    (report : Report state) :
    GeneralNominalState.Models state model ∧
    ¬ Models state declaration capture report (generated state interpretation [request]) model
```


## GeneralDictionaryFiniteObservedExampleReservedPositive

[Source](../../lean/Yulang/GeneralDictionaryFiniteObservedExampleReservedPositive.lean)

### positive_source

Side: soundness / auxiliary.

```lean
theorem positive_source : GeneralNominalState.Models state positive
```

### positive_request

Side: soundness / auxiliary.

```lean
theorem positive_request (capture : GeneralDeclarationDemands.Capture) (report : Report state) :
    Models state declaration capture report (generated state interpretation [request]) positive
```

### report_exact

Side: soundness / auxiliary.

```lean
theorem report_exact : report context declaration [(1,1)] =
    { inspected
```

### branch_models

Side: soundness / auxiliary.

```lean
theorem branch_models :
    BranchModels registry context root declaration checked [(1,1)] positive
```

### ready

Side: soundness / auxiliary.

```lean
theorem ready : RequestReady registry context root declaration checked [(1,1)]
```

### no_root

Side: soundness / auxiliary.

```lean
theorem no_root : ¬ GeneralNominalFeedbackK2.RootK2 start.current root
```

### no_candidate

Side: soundness / auxiliary.

```lean
theorem no_candidate : ¬ GeneralNominalFeedbackK2.CandidateK2 registry start.current root
```

### root_ready

Side: soundness / auxiliary.

```lean
theorem root_ready : ¬ GeneralNominalState.RootPending state root.demand
```

### prepared

Side: soundness / auxiliary.

```lean
theorem prepared : Prepared registry context root declaration checked
```

### children_empty

Side: soundness / auxiliary.

```lean
theorem children_empty : GeneralNominalAllocation.children state registry root declaration checked
    (bindings state (report context declaration [(1,1)])) = []
```

### survivor

Side: soundness / auxiliary.

```lean
theorem survivor : Survivor registry context root declaration.id []
```

### unique

Side: soundness / auxiliary.

```lean
theorem unique : GeneralNominalLocalBoundary.Unique (GeneralNominalFeedbackK2.fields roles)
    registry start.current root declaration.id []
```

### selected

Side: soundness / auxiliary.

```lean
theorem selected : GeneralNominalFeedbackK2.Local registry start.current root
    (.selected declaration.id [])
```

### decisions

Side: soundness / auxiliary.

```lean
theorem decisions : DecisionGuard start registry root []
```

### joint

Side: soundness / auxiliary.

```lean
theorem joint : GeneralNominalJointCandidates.Joint registry start.current root declaration.id
```

### packet_children

Side: soundness / auxiliary.

```lean
theorem packet_children : packet.children = []
```

### enabled

Side: soundness / auxiliary.

```lean
theorem enabled : GeneralNominalFeedbackSteps.Installable registry start.current packet
```

### novel

Side: soundness / auxiliary.

```lean
theorem novel : ¬ GeneralNominalFeedbackSteps.Committed start.current packet
```

### guard

Side: soundness / auxiliary.

```lean
theorem guard : GeneralNominalSupportSteps.PacketGuard start packet []
```

### value_install_step

Side: soundness / auxiliary.

```lean
theorem value_install_step : GeneralNominalValueSteps.Step registry root start installed
```

### installed_models

Side: soundness / auxiliary.

```lean
theorem installed_models : GeneralNominalSaturationState.Models installed.current positive
```

### value_reachable

Side: soundness / auxiliary.

```lean
theorem value_reachable :
    B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root installed
```

### packet_recorded

Side: soundness / auxiliary.

```lean
theorem packet_recorded : packet ∈ installed.current.packets
```

### journal_nonempty

Side: soundness / auxiliary.

```lean
theorem journal_nonempty : installed.current.packets ≠ []
```


## GeneralDictionaryFiniteObservedExampleReservedRecorded

[Source](../../lean/Yulang/GeneralDictionaryFiniteObservedExampleReservedRecorded.lean)

### recorded_request_models

Side: soundness / auxiliary.

```lean
theorem recorded_request_models (capture : GeneralDeclarationDemands.Capture)
    (report : GeneralNominalRecursiveInspection.Report installed.current.context.state)
    (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalSaturationState.Models installed.current assignment) :
    Models installed.current.context.state declaration capture report
      (generated installed.current.context.state installed.current.context.interpretation [request]) assignment
```

### reserved_install_regression

Side: soundness / auxiliary.

```lean
theorem reserved_install_regression :
    (¬ ∃ slot : Fin state.base.slots, state.base.source slot = 2) ∧
    (¬ GeneralDictionaryObservedFiniteRequests.Observed state interpretation [request]) ∧
    GeneralNominalValueSteps.Step registry root start installed ∧
    GeneralNominalSaturationState.Models installed.current positive ∧
    installed.current.packets ≠ []
```


## GeneralDictionaryFiniteObservedExampleStable

[Source](../../lean/Yulang/GeneralDictionaryFiniteObservedExampleStable.lean)

### initial_models

Side: soundness / auxiliary.

```lean
theorem initial_models (m : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models state m) : Models start.current m
```

### generated_root

Side: soundness / auxiliary.

```lean
theorem generated_root (focus : GeneralSourceDictionaries.Occurrence roles)
    (reached : Generated start.current root focus) : focus = root
```

### installs_committed

Side: soundness / auxiliary.

```lean
theorem installs_committed (p : Packet roles)
    (reached : Generated start.current root p.site.occurrence)
    (enabled : GeneralNominalFeedbackSteps.Installable registry start.current p) :
    GeneralNominalFeedbackSteps.Committed start.current p
```

### varying_source

Side: soundness / auxiliary.

```lean
theorem varying_source (name : Nat) (large : 2 ≤ name) : GeneralNominalState.Models state (varying name)
```

### refresh_large_unknown

Side: soundness / auxiliary.

```lean
theorem refresh_large_unknown (next : Context)
    (certificate : GeneralNominalCycleSteps.Refresh start.current next) (id : Nat) (large : 2 ≤ id) :
    ¬ GeneralNominalState.Known next.state id
```

### point_closed

Side: soundness / auxiliary.

```lean
theorem point_closed : GeneralNominalReobservationSteps.PointClosed state
```

### feedback_stable

Side: soundness / auxiliary.

```lean
theorem feedback_stable : GeneralNominalFeedbackSteps.Stable registry start.current root
```

### stable

Side: soundness / auxiliary.

```lean
theorem stable : GeneralNominalSupportSteps.Stable registry start root
```

### stable_reachable_named_dictionary

Side: soundness / auxiliary.

```lean
theorem stable_reachable_named_dictionary :
    B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry root start ∧
    Models start.current model ∧ GeneralNominalSupportSteps.Stable registry start root ∧
    root.demand.outputs ≠ [] ∧
    ∀ assignment, Models start.current assignment →
      GeneralDictionaryRecursiveEvidence.Evidence registry context assignment root (.node declaration.id [])
```

