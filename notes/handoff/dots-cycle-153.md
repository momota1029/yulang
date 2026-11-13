# Cycle 153 recovery and verified partial results

B4Bridges V5: 8 / 14 fields unresolved; six supplied. evidenceNode is still open.

## Scope
Recovered the interrupted cycle started 2026-11-13T00:24:43Z. Only work/dots-main is published. Source checkpoint integration cfd5dda4f is retained through ab59232e. Recovery freshly read orders/inbox at integration e8ec5bc4761798c84d16628e8e9bbd2ed9014f68; ACTIVE I-25, no new instruction. This later integration is not merged in this recovery, to avoid unvalidated changes before the deadline.

Four new modules connect arbitrary finite nominal-arity observations to branch Models, selected instances, alias Joint and conditional stable finite dictionary evidence. The transport module preserves certificates through actual ordinary and certified view-preserving refresh traces. These are conditional soundness/auxiliary results, not completion of general Evidence. Closed queries, point edges, existing targets, alias coverage, ordinary-trace/refresh conditions and stability remain explicit. No language semantics are changed.

## Verification
Recovery focused build: PASS, 747 jobs. Audit/Cycle153.lean with --trust=0: PASS. Complete declaration dependency gate: PASS, 62 declarations, only propext/Classical.choice/Quot.sound. git diff --check: PASS. No full build or full audit was run, per standing orders. No new Yulang2 execution/parser check; proof-only extensions of existing definitions, not a new behavior equivalence claim. Usage quota unknown.

## Interruption and limitations
The original agent vanished during environment reset. No active Lean/Lake/git writer remained. Remote last heartbeat was 00:26:50Z and head ab59232e. Periodic heartbeats and intermediate source publication were missed; this is a workflow failure, not successful compliance. Local committed four-module checkpoint survived and was revalidated. Untracked finite example and refinement-transport drafts remain unverified and unpublished. No complete non-scalar named-output successful-program fixture was recovered.

## Next
1. Derive alias coverage for general reachable states, rather than assume it.
2. Complete a non-scalar named-output InitialSource/Reachable/Stable/Classify/Evidence fixture.
3. Merge the newer integration before further work; preserve the four verified modules.

## Exact theorem types (soundness or auxiliary, conditional as written)

### lean/Yulang/GeneralDictionaryFiniteAliasJoint.lean
```lean
theorem shape_of_closed (context : GeneralNominalCandidates.Context) (registry : Registry)
    (focus : Occurrence roles) (chosen : Declaration)
    (checked : DeclarationChecked registry.constructors roles chosen)
    (shape : GeneralDictionaryClosedAliasJoint.Shape context registry focus chosen checked) :
    Shape context registry focus chosen checked

theorem covered_of_closed (registry : Registry) (state : Tracked roles) (focus : Occurrence roles)
    (chosen : Declaration) (checked : DeclarationChecked registry.constructors roles chosen)
    (covered : GeneralDictionaryClosedAliasJoint.Covered registry state focus chosen checked) :
    Covered registry state focus chosen checked

theorem selected_branch (registry : Registry) (state : Tracked roles) (focus : Occurrence roles)
    (chosen : Declaration) (visible : chosen ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles chosen)
    (shape : Shape state.current.context registry focus chosen checked)
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalSupportBoundary.Local registry state focus (.selected key children))
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    chosen.id = key ∧ BranchAt registry state.current focus chosen.id model

theorem covered_joint (registry : Registry) (root focus : Occurrence roles) (state : Tracked roles)
    (formed : SourceFormed registry root state)
    (growth : ∀ packet ∈ state.current.packets,
      GeneralDictionaryOrdinaryTrace.Extension packet.context state.current.context)
    (chosen : Declaration) (visible : chosen ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles chosen)
    (shape : Shape state.current.context registry focus chosen checked)
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalSupportBoundary.Local registry state focus (.selected key children))
    (covered : Covered registry state focus chosen checked)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    Joint registry state.current focus key

theorem ordinary_stable_evidence (registry : Registry) (root focus : Occurrence roles)
    (context : GeneralNominalCandidates.Context)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (state : Tracked roles)
    (path : B4Target.Steps (GeneralDictionarySupportOrdinaryExecution.Step registry root)
      (GeneralNominalSupport.initial context root) state)
    (stable : Stable registry state focus)
    (chosen : Declaration) (visible : chosen ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles chosen)
    (shape : Shape state.current.context registry focus chosen checked)
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalSupportBoundary.Local registry state focus (.selected key children))
    (covered : Covered registry state focus chosen checked)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model)
    (dictionaries : List GeneralDictionaryReadback.Payload)
    (given : CommonRoleOutermostResolver.All₂
      (GeneralDictionaryRecursiveEvidence.Evidence registry state.current.context model) children dictionaries) :
    GeneralDictionaryRecursiveEvidence.Evidence registry state.current.context model focus (.node key dictionaries)

```

### lean/Yulang/GeneralDictionaryFiniteStableCoverage.lean
```lean
theorem covered_of_closed (registry : Registry) (state : Tracked roles) (root : Occurrence roles)
    (covered : GeneralDictionaryClosedStableCoverage.Covered registry state root) :
    Covered registry state root

theorem initial_trace_joint (registry : Registry) (root focus : Occurrence roles)
    (context : GeneralNominalCandidates.Context)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (state : Tracked roles)
    (path : B4Target.Steps (GeneralDictionarySupportOrdinaryExecution.Step registry root)
      (GeneralNominalSupport.initial context root) state)
    (chosen : Declaration) (visible : chosen ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles chosen)
    (shape : GeneralDictionaryFiniteAliasJoint.Shape state.current.context registry focus chosen checked)
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalSupportBoundary.Local registry state focus (.selected key children))
    (covered : GeneralDictionaryFiniteAliasJoint.Covered registry state focus chosen checked)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    GeneralNominalJointCandidates.Joint registry state.current focus key

theorem stable_instances_generated (registry : Registry) (root focus : Occurrence roles)
    (context : GeneralNominalCandidates.Context)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (state : Tracked roles)
    (path : B4Target.Steps (GeneralDictionarySupportOrdinaryExecution.Step registry root)
      (GeneralNominalSupport.initial context root) state)
    (chosen : Declaration) (visible : chosen ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles chosen)
    (shape : GeneralDictionaryFiniteAliasJoint.Shape state.current.context registry focus chosen checked)
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalSupportBoundary.Local registry state focus (.selected key children))
    (covered : GeneralDictionaryFiniteAliasJoint.Covered registry state focus chosen checked)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model)
    (stable : Stable registry state focus) :
    (∀ assignment, Models state.current assignment →
      Instance registry state.current.context assignment focus key children) ∧
      ∀ child ∈ children, Generated state.current focus child

theorem covered_of_observed (registry : Registry) (state : Tracked roles)
    (root : Occurrence roles)
    (covered : GeneralDictionaryObservedStableCoverage.Covered registry state root) :
    Covered registry state root

theorem stable_descendant (registry : Registry) (state : Tracked roles)
    (root focus : Occurrence roles) (stable : Stable registry state root)
    (reached : Generated state.current root focus) : Stable registry state focus

theorem selected_instance_children (registry : Registry) (root focus : Occurrence roles)
    (context : GeneralNominalCandidates.Context)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (state : Tracked roles)
    (path : B4Target.Steps (GeneralDictionarySupportOrdinaryExecution.Step registry root)
      (GeneralNominalSupport.initial context root) state)
    (stable : Stable registry state root) (covered : Covered registry state root)
    (reached : Generated state.current root focus)
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalSupportBoundary.Local registry state focus (.selected key children))
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    Instance registry state.current.context model focus key children ∧
      ∀ child ∈ children, Generated state.current root child

theorem root_dictionary_all_models (registry : Registry) (root : Occurrence roles)
    (context : GeneralNominalCandidates.Context)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (state : Tracked roles)
    (path : B4Target.Steps (GeneralDictionarySupportOrdinaryExecution.Step registry root)
      (GeneralNominalSupport.initial context root) state)
    (stable : Stable registry state root) (covered : Covered registry state root)
    (dictionary : GeneralDictionaryReadback.Payload)
    (derived : B4TargetV3.Classify (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary
      registry state root (.selected dictionary)) :
    ∀ model, Models state.current model →
      Evidence registry state.current.context model root dictionary

theorem covered_descendant (registry : Registry) (state : Tracked roles)
    (root focus : Occurrence roles) (covered : Covered registry state root)
    (reached : Generated state.current root focus) : Covered registry state focus

```

### lean/Yulang/GeneralDictionaryFiniteTreeBranch.lean
```lean
theorem branch_models (context : Context) (registry : Registry) (root : Occurrence roles)
    (declaration : Declaration) (checked : DeclarationChecked registry.constructors roles declaration)
    (shape : Shape context registry root declaration checked)
    (model : GeneralNominalCommonBridge.Assignment) (valid : GeneralNominalState.Models context.state model) :
    BranchModels registry context root declaration checked [(shape.slot,shape.slot)] model

theorem ready (context : Context) (registry : Registry) (root : Occurrence roles)
    (declaration : Declaration) (checked : DeclarationChecked registry.constructors roles declaration)
    (shape : Shape context registry root declaration checked) :
    RequestReady registry context root declaration checked [(shape.slot,shape.slot)]

theorem instance_of_shape (context : Context) (registry : Registry) (root : Occurrence roles)
    (declaration : Declaration) (visible : declaration ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (shape : Shape context registry root declaration checked)
    (metadata : Metadata registry context) (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models context.state model) :
    Instance registry context model root declaration.id
      (GeneralNominalAllocation.children context.state registry root declaration checked
        (bindings context.state (report context declaration [(shape.slot,shape.slot)])))

theorem selected_instance (registry : Registry) (state : GeneralNominalSaturationState.State roles)
    (root : Occurrence roles) (declaration : Declaration) (visible : declaration ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (shape : Shape state.context registry root declaration checked)
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalFeedbackK2.Local registry state root (.selected key children))
    (model : GeneralNominalCommonBridge.Assignment) (valid : GeneralNominalState.Models state.context.state model) :
    declaration.id = key ∧ Instance registry state.context model root key children

```

### lean/Yulang/GeneralDictionaryObservedRefreshTransport.lean
```lean
theorem observed_reobserve (context : Context) (next : Observation context.state)
    (view : next.view = context.state.view)
    (refinement : GeneralNominalRefinements.Refines context.state (reobserve context next).state)
    (requests : List Request) (observed : Observed context.state context.interpretation requests) :
    Observed (reobserve context next).state (reobserve context next).interpretation requests

theorem observed_extension (before after : Context)
    (growth : GeneralDictionaryOrdinaryTrace.Extension before after) (requests : List Request)
    (observed : Observed before.state before.interpretation requests) :
    Observed after.state after.interpretation requests

theorem observed_step {roles : Roles.RoleDecls} (registry : GeneralDeclarations.Registry)
    (root : GeneralSourceDictionaries.Occurrence roles)
    (before after : GeneralNominalSaturationState.State roles)
    (step : GeneralDictionaryFinishedTrace.Step registry root before after)
    (requests : List Request)
    (observed : Observed before.context.state before.context.interpretation requests) :
    Observed after.context.state after.context.interpretation requests

theorem observed_trace {roles : Roles.RoleDecls} (registry : GeneralDeclarations.Registry)
    (root : GeneralSourceDictionaries.Occurrence roles)
    (before after : GeneralNominalSaturationState.State roles)
    (path : B4Target.Steps (GeneralDictionaryFinishedTrace.Step registry root) before after)
    (requests : List Request)
    (observed : Observed before.context.state before.context.interpretation requests) :
    Observed after.context.state after.context.interpretation requests

theorem generated_models_after_trace {roles : Roles.RoleDecls}
    (registry : GeneralDeclarations.Registry) (root : GeneralSourceDictionaries.Occurrence roles)
    (before after : GeneralNominalSaturationState.State roles)
    (path : B4Target.Steps (GeneralDictionaryFinishedTrace.Step registry root) before after)
    (requests : List Request)
    (observed : Observed before.context.state before.context.interpretation requests)
    (declaration : GeneralDeclarations.Declaration) (capture : GeneralDeclarationDemands.Capture)
    (report : GeneralNominalRecursiveInspection.Report after.context.state)
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models after.context.state model) :
    Models after.context.state declaration capture report
      (generated after.context.state after.context.interpretation requests) model

theorem actual_requests_models_after_trace {roles : Roles.RoleDecls}
    (registry : GeneralDeclarations.Registry) (root : GeneralSourceDictionaries.Occurrence roles)
    (before after : GeneralNominalSaturationState.State roles)
    (path : B4Target.Steps (GeneralDictionaryFinishedTrace.Step registry root) before after)
    (declaration : GeneralDeclarations.Declaration)
    (checked : GeneralDeclarations.DeclarationChecked registry.constructors roles declaration)
    (captures : GeneralNominalAllocation.Bindings)
    (variables : GeneralDictionaryVariableRequirements.VariableClauses declaration)
    (observed : Observed before.context.state before.context.interpretation (rootRequests declaration root))
    (capture : GeneralDeclarationDemands.Capture)
    (report : GeneralNominalRecursiveInspection.Report after.context.state)
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models after.context.state model) :
    Models after.context.state declaration capture report
      (generated after.context.state after.context.interpretation
        (requests after.context.state registry root declaration checked captures)) model

theorem generated_shape_after_trace {roles : Roles.RoleDecls}
    (registry : GeneralDeclarations.Registry) (root : GeneralSourceDictionaries.Occurrence roles)
    (before after : GeneralNominalSaturationState.State roles)
    (path : B4Target.Steps (GeneralDictionaryFinishedTrace.Step registry root) before after)
    (requests : List Request)
    (observed : Observed before.context.state before.context.interpretation requests) :
    (generated after.context.state after.context.interpretation requests).variables = [] ∧
    (generated after.context.state after.context.interpretation requests).unknown = false

```

## Validation output

### recovery-build.log
```text
Build completed successfully (747 jobs).
```

### recovery-audit.log
```text
'Yulang.GeneralDictionaryFiniteAliasJoint.shape_of_closed' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryFiniteAliasJoint.covered_of_closed' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryFiniteAliasJoint.selected_branch' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryFiniteAliasJoint.covered_joint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryFiniteAliasJoint.ordinary_stable_evidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteStableCoverage.covered_of_closed' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryFiniteStableCoverage.initial_trace_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteStableCoverage.stable_instances_generated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteStableCoverage.covered_of_observed' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryFiniteStableCoverage.stable_descendant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteStableCoverage.selected_instance_children' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteStableCoverage.root_dictionary_all_models' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteStableCoverage.covered_descendant' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryFiniteTreeBranch.branch_models' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryFiniteTreeBranch.ready' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryFiniteTreeBranch.instance_of_shape' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryFiniteTreeBranch.selected_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryObservedRefreshTransport.tree_reobserve' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryObservedRefreshTransport.observed_reobserve' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryObservedRefreshTransport.tree_extension' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryObservedRefreshTransport.observed_extension' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryObservedRefreshTransport.observed_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryObservedRefreshTransport.observed_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryObservedRefreshTransport.generated_models_after_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryObservedRefreshTransport.actual_requests_models_after_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryObservedRefreshTransport.generated_shape_after_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### recovery-gate.log
```text
FOCUSED-AXIOM-PASS: 62 declarations in cycle153 modules
```

## Boundary inventory
| Item | Status |
|---|---|
| Checked | General nominal declaration definition; full-language fidelity separate |
| Models | General definition |
| RootPending | General definition |
| RootK2 | General definition |
| CandidateK2 | General definition |
| InspectionPending | General definition |
| Survivor | General nominal candidate definition |
| Reorders | General definition |
| DictionaryEquivalent | General definition |
| Step | General definition, Astra-owned and unchanged |
| Stable | General definition, unchanged |
| Generated | General definition, unchanged |
| Evidence | General definition; general evidenceNode bridge open |

Remaining eight: progress, execution, halted, whereAccessible, treeExecution, canonicalLocalOrder, evidenceNode, generatedChildren.

## Publication readback
Source/report checkpoint a4c726e262a8fa0d712172c564447d1851cdb6b9 was published non-force with expected head ab59232e. Its tree is 18253e9551e630704be12bf21708e474cfbad697. All ten changed paths were retrieved byte-for-byte and match. The local INDEX-only four-line addition was omitted; the new audit imports all four modules directly. There are 24 new theorem declarations and 26 explicit audit checks; the complete dependency gate checks 62 declarations including definitions. No full CI claim is made.
