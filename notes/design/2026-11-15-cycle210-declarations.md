# Cycle210 exact declaration types

86 theorem declarations,20 new modules. Generated with Lean4.35 kernel trust0
and warning-as-error. These are the actual quantified types, not claims of
unrestricted EvidenceNode/FreshCompletion.

```text
Yulang.GeneralDictionaryDefaultExistentialReplay210.nominal_instance {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalCenteredHeadMatStepJournal.State roles}
  {current historical : Yulang.GeneralNominalCenters.Plan roles}
  {value : (Yulang.GeneralNominalCenteredHeadMatStepLocal.vocabulary roles).Registry}
  {root : (Yulang.GeneralNominalCenteredHeadMatStepLocal.vocabulary roles).Demand}
  {focus : Yulang.GeneralSourceDictionaries.Occurrence roles} {key : Nat}
  {model : Yulang.GeneralNominalCommonBridge.Assignment}
  (checked : (Yulang.GeneralDictionaryDefaultBoundary208.boundary roles).Checked value)
  (reachable : Yulang.B4TargetV7.Reachable (Yulang.GeneralDictionaryDefaultBoundary208.boundary roles) value root state)
  (frame :
    Yulang.GeneralNominalCenteredHeadOutputs.Frame (Yulang.GeneralNominalCenteredHeadAllocEncoding.registry value)
      state.core focus key current)
  (member : historical ∈ state.core.plans) (keyEq : historical.packet.declaration.id = key)
  (occurrence : historical.packet.site.occurrence = focus)
  (refinement : Yulang.GeneralNominalRefinements.Refines historical.packet.context.state current.packet.context.state)
  (shape :
    ∀ (query : Yulang.GeneralNominalInspection.Query),
      query ∈
          Yulang.GeneralNominalInspection.queries historical.packet.context.state
            historical.packet.context.interpretation historical.packet.declaration →
        Yulang.GeneralNominalFinishedObservation197.Syntax query)
  (valid : Yulang.GeneralNominalCenteredHeadMatStepJournal.Models state model) :
  Yulang.GeneralDictionaryTotalEvidence206.Instance (Yulang.GeneralNominalCenteredHeadAllocEncoding.registry value)
    state.core model focus key current.packet.children
Yulang.GeneralDictionaryDefaultExistentialReplay210.nominal_evidence {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalCenteredHeadMatStepJournal.State roles}
  {current historical : Yulang.GeneralNominalCenters.Plan roles}
  {value : (Yulang.GeneralNominalCenteredHeadMatStepLocal.vocabulary roles).Registry}
  {root : (Yulang.GeneralNominalCenteredHeadMatStepLocal.vocabulary roles).Demand}
  {focus : Yulang.GeneralSourceDictionaries.Occurrence roles} {key : Nat}
  {model : Yulang.GeneralNominalCommonBridge.Assignment} {dictionaries : List Yulang.GeneralDictionaryReadback.Payload}
  (checked : (Yulang.GeneralDictionaryDefaultBoundary208.boundary roles).Checked value)
  (reachable : Yulang.B4TargetV7.Reachable (Yulang.GeneralDictionaryDefaultBoundary208.boundary roles) value root state)
  (frame :
    Yulang.GeneralNominalCenteredHeadOutputs.Frame (Yulang.GeneralNominalCenteredHeadAllocEncoding.registry value)
      state.core focus key current)
  (member : historical ∈ state.core.plans) (keyEq : historical.packet.declaration.id = key)
  (occurrence : historical.packet.site.occurrence = focus)
  (refinement : Yulang.GeneralNominalRefinements.Refines historical.packet.context.state current.packet.context.state)
  (shape :
    ∀ (query : Yulang.GeneralNominalInspection.Query),
      query ∈
          Yulang.GeneralNominalInspection.queries historical.packet.context.state
            historical.packet.context.interpretation historical.packet.declaration →
        Yulang.GeneralNominalFinishedObservation197.Syntax query)
  (valid : Yulang.GeneralNominalCenteredHeadMatStepJournal.Models state model)
  (given :
    Yulang.CommonRoleOutermostResolver.All₂
      (Yulang.GeneralDictionaryTotalEvidence206.Evidence (Yulang.GeneralNominalCenteredHeadAllocEncoding.registry value)
        state.core model)
      current.packet.children dictionaries) :
  Yulang.GeneralDictionaryTotalEvidence206.Evidence (Yulang.GeneralNominalCenteredHeadAllocEncoding.registry value)
    state.core model focus (Yulang.CommonRoleOutermostResolver.Dictionary.node key dictionaries)
Yulang.GeneralDictionaryDefaultExistentialReplay210.selected_nominal_evidence {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalCenteredHeadMatStepJournal.State roles}
  {historical : Yulang.GeneralNominalCenters.Plan roles}
  {value : (Yulang.GeneralNominalCenteredHeadMatStepLocal.vocabulary roles).Registry}
  {root focus : (Yulang.GeneralNominalCenteredHeadMatStepLocal.vocabulary roles).Demand} {key : Nat}
  {children : List (Yulang.GeneralNominalCenteredHeadMatStepLocal.vocabulary roles).Demand}
  {model : Yulang.GeneralNominalCommonBridge.Assignment} {dictionaries : List Yulang.GeneralDictionaryReadback.Payload}
  (checked : (Yulang.GeneralDictionaryDefaultBoundary208.boundary roles).Checked value)
  (reachable : Yulang.B4TargetV7.Reachable (Yulang.GeneralDictionaryDefaultBoundary208.boundary roles) value root state)
  (selected :
    Yulang.GeneralDictionaryDefaultBoundary208.Local value state focus
      (Yulang.CommonRoleOutermostResolver.Frontier.selected key children))
  (member : historical ∈ state.core.plans) (keyEq : historical.packet.declaration.id = key)
  (occurrence : historical.packet.site.occurrence = focus)
  (refinement :
    Yulang.GeneralNominalRefinements.Refines historical.packet.context.state state.core.erased.current.context.state)
  (shape :
    ∀ (query : Yulang.GeneralNominalInspection.Query),
      query ∈
          Yulang.GeneralNominalInspection.queries historical.packet.context.state
            historical.packet.context.interpretation historical.packet.declaration →
        Yulang.GeneralNominalFinishedObservation197.Syntax query)
  (valid : Yulang.GeneralNominalCenteredHeadMatStepJournal.Models state model)
  (given :
    Yulang.CommonRoleOutermostResolver.All₂
      (Yulang.GeneralDictionaryTotalEvidence206.Evidence (Yulang.GeneralNominalCenteredHeadAllocEncoding.registry value)
        state.core model)
      children dictionaries) :
  Yulang.GeneralDictionaryTotalEvidence206.Evidence (Yulang.GeneralNominalCenteredHeadAllocEncoding.registry value)
    state.core model focus (Yulang.CommonRoleOutermostResolver.Dictionary.node key dictionaries)
Yulang.GeneralDictionaryDefaultExistentialReplay210.selected_nominal_generated {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalCenteredHeadMatStepJournal.State roles}
  {historical : Yulang.GeneralNominalCenters.Plan roles}
  {value : (Yulang.GeneralNominalCenteredHeadMatStepLocal.vocabulary roles).Registry}
  {root focus : (Yulang.GeneralNominalCenteredHeadMatStepLocal.vocabulary roles).Demand} {key : Nat}
  {children : List (Yulang.GeneralNominalCenteredHeadMatStepLocal.vocabulary roles).Demand}
  {child : (Yulang.GeneralNominalCenteredHeadMatStepLocal.vocabulary roles).Demand}
  (checked : (Yulang.GeneralDictionaryDefaultBoundary208.boundary roles).Checked value)
  (reachable : Yulang.B4TargetV7.Reachable (Yulang.GeneralDictionaryDefaultBoundary208.boundary roles) value root state)
  (selected :
    Yulang.GeneralDictionaryDefaultBoundary208.Local value state focus
      (Yulang.CommonRoleOutermostResolver.Frontier.selected key children))
  (member : historical ∈ state.core.plans) (keyEq : historical.packet.declaration.id = key)
  (occurrence : historical.packet.site.occurrence = focus)
  (refinement :
    Yulang.GeneralNominalRefinements.Refines historical.packet.context.state state.core.erased.current.context.state)
  (shape :
    ∀ (query : Yulang.GeneralNominalInspection.Query),
      query ∈
          Yulang.GeneralNominalInspection.queries historical.packet.context.state
            historical.packet.context.interpretation historical.packet.declaration →
        Yulang.GeneralNominalFinishedObservation197.Syntax query)
  (reached :
    focus = root ∨ (Yulang.GeneralDictionaryDefaultBoundary208.boundary roles).Generated value state root focus)
  (childMember : child ∈ children) :
  (Yulang.GeneralDictionaryDefaultBoundary208.boundary roles).Generated value state root child
Yulang.GeneralDictionaryDefaultMergeRevisionGuard210.head_models_excluded {upper : Nat} {roles : Yulang.Roles.RoleDecls}
  {root : Yulang.GeneralSourceDictionaries.Occurrence roles} {name : Nat}
  {context : Yulang.GeneralNominalRecursiveCandidates.Context} {declaration : Yulang.GeneralDeclarations.Declaration}
  {bounds : List (Yulang.GeneralNominalInspection.Bounds context.state)} {last nextUpper : Nat}
  {registry : Yulang.GeneralDeclarations.Registry} {first : Nat} (named : name ∈ declaration.inputNames)
  (newBindings :
    Yulang.GeneralNominalRecursiveInspection.bindings context.state
        (Yulang.GeneralNominalRecursiveCandidates.report context declaration bounds) =
      Yulang.GeneralDictionaryDefaultMergeRevisionProbe210.twice name last nextUpper)
  (oldRaw :
    ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
      Yulang.GeneralNominalState.Models context.state model →
        Yulang.PresenceNormalForm.All Yulang.CommonNominalFullCarrier.model model
          (Yulang.GeneralNominalAllocation.merges context.state registry root.identity declaration
            (Yulang.GeneralDictionaryDefaultMergeRevisionProbe210.twice name first upper)))
  (separated :
    ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
      Yulang.GeneralNominalState.Models context.state model →
        (model first).fst = Yulang.CommonNominalSyntax.Layer.bottom ∧
          (model last).fst = Yulang.CommonNominalSyntax.Layer.base Yulang.Inference.Base.int) :
  ¬∃ model, Yulang.GeneralNominalCenteredHeadCandidates.HeadModels registry context root declaration bounds model
Yulang.GeneralDictionaryDefaultMergeRevisionGuard210.prepared_excluded {upper : Nat} {roles : Yulang.Roles.RoleDecls}
  {root : Yulang.GeneralSourceDictionaries.Occurrence roles} {name : Nat}
  {context : Yulang.GeneralNominalRecursiveCandidates.Context}
  {bounds : List (Yulang.GeneralNominalInspection.Bounds context.state)}
  {declaration : Yulang.GeneralDeclarations.Declaration} {last nextUpper : Nat}
  {registry : Yulang.GeneralDeclarations.Registry} {first : Nat} (named : name ∈ declaration.inputNames)
  (located :
    Yulang.GeneralNominalRecursiveCandidates.arguments context
        (Yulang.GeneralNominalCenteredHeadCandidates.inputs root) =
      some bounds)
  (newBindings :
    Yulang.GeneralNominalRecursiveInspection.bindings context.state
        (Yulang.GeneralNominalRecursiveCandidates.report context declaration bounds) =
      Yulang.GeneralDictionaryDefaultMergeRevisionProbe210.twice name last nextUpper)
  (oldRaw :
    ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
      Yulang.GeneralNominalState.Models context.state model →
        Yulang.PresenceNormalForm.All Yulang.CommonNominalFullCarrier.model model
          (Yulang.GeneralNominalAllocation.merges context.state registry root.identity declaration
            (Yulang.GeneralDictionaryDefaultMergeRevisionProbe210.twice name first upper)))
  (separated :
    ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
      Yulang.GeneralNominalState.Models context.state model →
        (model first).fst = Yulang.CommonNominalSyntax.Layer.bottom ∧
          (model last).fst = Yulang.CommonNominalSyntax.Layer.base Yulang.Inference.Base.int) :
  ¬Yulang.GeneralNominalCenteredHeadCandidates.Prepared registry context root declaration
Yulang.GeneralDictionaryDefaultMergeRevisionProbe210.repeated_lower {lower upper name : Nat}
  {state : Yulang.GeneralNominalState.State} {registry : Yulang.GeneralDeclarations.Registry} {root : Nat}
  {declaration : Yulang.GeneralDeclarations.Declaration} {model : Yulang.GeneralNominalCommonBridge.Assignment}
  (named : name ∈ declaration.inputNames)
  (holds :
    Yulang.PresenceNormalForm.All Yulang.CommonNominalFullCarrier.model model
      (Yulang.GeneralNominalAllocation.merges state registry root declaration
        (Yulang.GeneralDictionaryDefaultMergeRevisionProbe210.twice name lower upper))) :
  Yulang.CommonNominalFullCarrier.Equivalent
    (model
        (Yulang.GeneralNominalAllocation.source state registry root
          (Yulang.GeneralNominalAllocation.origin root declaration.id 0 name 0))).fst
    (Yulang.CommonNominalSyntax.Layer.union (model lower).fst (model lower).fst)
Yulang.GeneralDictionaryDefaultMergeRevisionProbe210.union_self (value : Yulang.CommonNominalFullCarrier.Ty) :
  Yulang.CommonNominalFullCarrier.Equivalent (Yulang.CommonNominalSyntax.Layer.union value value) value
Yulang.GeneralDictionaryDefaultMergeRevisionProbe210.repeated_lower_value {lower upper name : Nat}
  {state : Yulang.GeneralNominalState.State} {registry : Yulang.GeneralDeclarations.Registry} {root : Nat}
  {declaration : Yulang.GeneralDeclarations.Declaration} {model : Yulang.GeneralNominalCommonBridge.Assignment}
  (named : name ∈ declaration.inputNames)
  (holds :
    Yulang.PresenceNormalForm.All Yulang.CommonNominalFullCarrier.model model
      (Yulang.GeneralNominalAllocation.merges state registry root declaration
        (Yulang.GeneralDictionaryDefaultMergeRevisionProbe210.twice name lower upper))) :
  Yulang.CommonNominalFullCarrier.Equivalent
    (model
        (Yulang.GeneralNominalAllocation.source state registry root
          (Yulang.GeneralNominalAllocation.origin root declaration.id 0 name 0))).fst
    (model lower).fst
Yulang.GeneralDictionaryDefaultMergeRevisionProbe210.reused_lower_forces_equivalence {upper name : Nat}
  {state : Yulang.GeneralNominalState.State} {registry : Yulang.GeneralDeclarations.Registry} {root : Nat}
  {declaration : Yulang.GeneralDeclarations.Declaration} {first last nextUpper : Nat}
  {model : Yulang.GeneralNominalCommonBridge.Assignment} (named : name ∈ declaration.inputNames)
  (one :
    Yulang.PresenceNormalForm.All Yulang.CommonNominalFullCarrier.model model
      (Yulang.GeneralNominalAllocation.merges state registry root declaration
        (Yulang.GeneralDictionaryDefaultMergeRevisionProbe210.twice name first upper)))
  (two :
    Yulang.PresenceNormalForm.All Yulang.CommonNominalFullCarrier.model model
      (Yulang.GeneralNominalAllocation.merges state registry root declaration
        (Yulang.GeneralDictionaryDefaultMergeRevisionProbe210.twice name last nextUpper))) :
  Yulang.CommonNominalFullCarrier.Equivalent (model first).fst (model last).fst
Yulang.GeneralDictionaryDefaultMergeRevisionProbe210.bottom_int_incompatible {upper name first last : Nat}
  {state : Yulang.GeneralNominalState.State} {registry : Yulang.GeneralDeclarations.Registry} {root : Nat}
  {declaration : Yulang.GeneralDeclarations.Declaration} {nextUpper : Nat}
  {model : Yulang.GeneralNominalCommonBridge.Assignment} (named : name ∈ declaration.inputNames)
  (bottom : (model first).fst = Yulang.CommonNominalSyntax.Layer.bottom)
  (integer : (model last).fst = Yulang.CommonNominalSyntax.Layer.base Yulang.Inference.Base.int) :
  ¬(Yulang.PresenceNormalForm.All Yulang.CommonNominalFullCarrier.model model
        (Yulang.GeneralNominalAllocation.merges state registry root declaration
          (Yulang.GeneralDictionaryDefaultMergeRevisionProbe210.twice name first upper)) ∧
      Yulang.PresenceNormalForm.All Yulang.CommonNominalFullCarrier.model model
        (Yulang.GeneralNominalAllocation.merges state registry root declaration
          (Yulang.GeneralDictionaryDefaultMergeRevisionProbe210.twice name last nextUpper)))
Yulang.GeneralDictionaryDefaultMergeRevisionProbe210.changed_state_incompatible {upper name first last : Nat}
  {firstState : Yulang.GeneralNominalState.State} {registry : Yulang.GeneralDeclarations.Registry} {root : Nat}
  {declaration : Yulang.GeneralDeclarations.Declaration} {lastState : Yulang.GeneralNominalState.State}
  {nextUpper : Nat} {model : Yulang.GeneralNominalCommonBridge.Assignment} (sameSeed : firstState.seed = lastState.seed)
  (named : name ∈ declaration.inputNames) (bottom : (model first).fst = Yulang.CommonNominalSyntax.Layer.bottom)
  (integer : (model last).fst = Yulang.CommonNominalSyntax.Layer.base Yulang.Inference.Base.int) :
  ¬(Yulang.PresenceNormalForm.All Yulang.CommonNominalFullCarrier.model model
        (Yulang.GeneralNominalAllocation.merges firstState registry root declaration
          (Yulang.GeneralDictionaryDefaultMergeRevisionProbe210.twice name first upper)) ∧
      Yulang.PresenceNormalForm.All Yulang.CommonNominalFullCarrier.model model
        (Yulang.GeneralNominalAllocation.merges lastState registry root declaration
          (Yulang.GeneralDictionaryDefaultMergeRevisionProbe210.twice name last nextUpper)))
Yulang.GeneralDictionaryDefaultMergeRevisionProbe210.packet_reinspection_impossible {upper : Nat}
  {roles : Yulang.Roles.RoleDecls} {name first last nextUpper : Nat}
  {old current : Yulang.GeneralNominalCenters.Plan roles} {model : Yulang.GeneralNominalCommonBridge.Assignment}
  (registryEq : old.packet.registry = current.packet.registry)
  (rootEq : old.packet.site.occurrence.identity = current.packet.site.occurrence.identity)
  (declarationEq : old.packet.declaration = current.packet.declaration)
  (sameSeed : old.packet.context.state.seed = current.packet.context.state.seed)
  (named : name ∈ old.packet.declaration.inputNames)
  (oldBindings : old.packet.bindings = Yulang.GeneralDictionaryDefaultMergeRevisionProbe210.twice name first upper)
  (newBindings :
    current.packet.bindings = Yulang.GeneralDictionaryDefaultMergeRevisionProbe210.twice name last nextUpper)
  (bottom : (model first).fst = Yulang.CommonNominalSyntax.Layer.bottom)
  (integer : (model last).fst = Yulang.CommonNominalSyntax.Layer.base Yulang.Inference.Base.int)
  (oldValid : Yulang.GeneralNominalCenteredHeadMatStepPackets.Holds old model) :
  ¬Yulang.GeneralNominalCenteredHeadMatStepPackets.Holds current model
Yulang.GeneralDictionaryDefaultReplayRegression210.retained_interval_body :
  Yulang.GeneralNominalCenteredHeadMatEffects.BodyHolds
    (Yulang.GeneralDictionaryDefaultSemanticReplay209.recenter
      (Yulang.GeneralDictionaryDefaultTransportExamples209.intervalPlan 1)
      (Yulang.GeneralDictionaryDefaultTransportExamples209.intervalSite 0) ⋯)
    0 Yulang.GeneralDictionaryDefaultTransportExamples209.intervalModel
    (Yulang.GeneralDictionaryAssociatedProvenance.Body.default 0 0 (Yulang.Roles.Term.var 0))
Yulang.GeneralDictionaryDefaultReplayRegression210.arbitrary_interval_body_fails :
  ¬Yulang.GeneralNominalCenteredHeadMatEffects.BodyHolds
      (Yulang.GeneralDictionaryDefaultTransportExamples209.intervalPlan 1) 0
      Yulang.GeneralDictionaryDefaultTransportExamples209.intervalModel
      (Yulang.GeneralDictionaryAssociatedProvenance.Body.default 0 0 (Yulang.Roles.Term.var 0))
Yulang.GeneralDictionaryDefaultReplayRegression210.centers_not_equal :
  (Yulang.GeneralDictionaryDefaultTransportExamples209.intervalSite 0).center 0 ≠
    (Yulang.GeneralDictionaryDefaultTransportExamples209.intervalSite 1).center 0
Yulang.GeneralDictionaryDefaultReplayRegression210.real_revision_changes_descriptor :
  (Yulang.GeneralNominalRefreshFork.state (some true)).nominals 0 ≠
    Yulang.GeneralNominalReobservationExamples.revision.snapshot.nominals 0
Yulang.GeneralDictionaryDefaultReplayRegression210.real_revision_certified :
  Yulang.GeneralNominalReobservationSteps.Certified Yulang.GeneralNominalReobservationExamples.revision
Yulang.GeneralDictionaryDefaultReplayRegression210.real_revision_improves :
  Yulang.GeneralNominalReobservationSteps.Improves Yulang.GeneralNominalReobservationExamples.revision
Yulang.GeneralDictionaryDefaultReplayRegression210.scalar_finished :
  Yulang.GeneralNominalRecursiveInspection.Finished
    (Yulang.GeneralNominalRecursiveInspection.inspect (Yulang.GeneralNominalRefreshFork.state (some true))
      (Yulang.GeneralNominalInspection.Query.scalar Yulang.Inference.Base.int) (3, 3) none)
Yulang.GeneralDictionaryDefaultReplayRegression210.scalar_traced :
  Yulang.GeneralNominalInspectionTrace197.Trace (Yulang.GeneralNominalRefreshFork.state (some true))
    (Yulang.GeneralDictionaryDefaultStructuralReobserve210.view Yulang.GeneralNominalReobservationExamples.revision)
    (Yulang.GeneralNominalInspection.Query.scalar Yulang.Inference.Base.int) (3, 3)
Yulang.GeneralDictionaryDefaultReplayRegression210.scalar_queries :
  Yulang.GeneralNominalInspection.queries (Yulang.GeneralNominalRefreshFork.state (some true))
      Yulang.GeneralNominalExamples.interpretation
      { id := 91, role := 0, head := [Yulang.GeneralDeclarationPatterns.Pattern.app 2 []], requirements := [],
        associated := [], outputBinders := [] } =
    [Yulang.GeneralNominalInspection.Query.scalar Yulang.Inference.Base.int]
Yulang.GeneralDictionaryDefaultReplayRegression210.scalar_candidate_report :
  Yulang.GeneralNominalReportErasure.erase Yulang.GeneralNominalReobservationExamples.revision.snapshot
      (Yulang.GeneralNominalRecursiveCandidates.report
        { state := Yulang.GeneralNominalReobservationExamples.revision.snapshot,
          interpretation := (Yulang.GeneralNominalRefreshFork.context (some true)).interpretation }
        { id := 91, role := 0, head := [Yulang.GeneralDeclarationPatterns.Pattern.app 2 []], requirements := [],
          associated := [], outputBinders := [] }
        [(3, 3)]) =
    Yulang.GeneralNominalReportErasure.erase (Yulang.GeneralNominalRefreshFork.state (some true))
      (Yulang.GeneralNominalRecursiveCandidates.report (Yulang.GeneralNominalRefreshFork.context (some true))
        { id := 91, role := 0, head := [Yulang.GeneralDeclarationPatterns.Pattern.app 2 []], requirements := [],
          associated := [], outputBinders := [] }
        [(3, 3)])
Yulang.GeneralDictionaryDefaultRetainedCenter210.stored_input_built {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalCenteredHeadMatStepJournal.State roles}
  {historical : Yulang.GeneralNominalCenters.Plan roles} {value : Yulang.GeneralDeclarations.Registry}
  {context : Yulang.GeneralNominalCandidates.Context} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  (built : Yulang.GeneralNominalCenteredHeadMatStepHistory.Built value context root state)
  (member : historical ∈ state.core.plans) : historical.input ∈ state.core.sites
Yulang.GeneralDictionaryDefaultRetainedCenter210.stored_input {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalCenteredHeadMatStepJournal.State roles}
  {historical : Yulang.GeneralNominalCenters.Plan roles}
  {value : (Yulang.GeneralNominalCenteredHeadMatStepLocal.vocabulary roles).Registry}
  {root : (Yulang.GeneralNominalCenteredHeadMatStepLocal.vocabulary roles).Demand}
  (reachable : Yulang.B4TargetV7.Reachable (Yulang.GeneralDictionaryDefaultBoundary208.boundary roles) value root state)
  (member : historical ∈ state.core.plans) : historical.input ∈ state.core.sites
Yulang.GeneralDictionaryDefaultRetainedCenter210.recenter_frame {roles : Yulang.Roles.RoleDecls}
  {current : Yulang.GeneralNominalCenters.Plan roles} {reg : Yulang.GeneralDeclarations.Registry}
  {core : Yulang.GeneralNominalCenteredSteps.State roles} {focus : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {key : Nat} (frame : Yulang.GeneralNominalCenteredHeadOutputs.Frame reg core focus key current)
  (site : Yulang.GeneralNominalCenters.Site roles) (recorded : site ∈ core.sites)
  (same : site.occurrence = current.packet.site.occurrence) :
  Yulang.GeneralNominalCenteredHeadOutputs.Frame reg core focus key
    (Yulang.GeneralDictionaryDefaultSemanticReplay209.recenter current site same)
Yulang.GeneralDictionaryDefaultRetainedCenter210.certificate {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalCenteredHeadMatStepJournal.State roles}
  {current historical : Yulang.GeneralNominalCenters.Plan roles}
  {value : (Yulang.GeneralNominalCenteredHeadMatStepLocal.vocabulary roles).Registry}
  {root : (Yulang.GeneralNominalCenteredHeadMatStepLocal.vocabulary roles).Demand}
  {focus : Yulang.GeneralSourceDictionaries.Occurrence roles} {key : Nat}
  {model : Yulang.GeneralNominalCommonBridge.Assignment}
  (checked : (Yulang.GeneralDictionaryDefaultBoundary208.boundary roles).Checked value)
  (reachable : Yulang.B4TargetV7.Reachable (Yulang.GeneralDictionaryDefaultBoundary208.boundary roles) value root state)
  (frame :
    Yulang.GeneralNominalCenteredHeadOutputs.Frame (Yulang.GeneralNominalCenteredHeadAllocEncoding.registry value)
      state.core focus key current)
  (member : historical ∈ state.core.plans) (keyEq : historical.packet.declaration.id = key)
  (occurrence : historical.packet.site.occurrence = focus)
  (report :
    Yulang.GeneralNominalReportErasure.erase current.packet.context.state
        (Yulang.GeneralNominalPacketSupport.report current.packet) =
      Yulang.GeneralNominalReportErasure.erase historical.packet.context.state
        (Yulang.GeneralNominalPacketSupport.report historical.packet))
  (valid : Yulang.GeneralNominalCenteredHeadMatStepJournal.Models state model) :
  ∃ witness,
    Yulang.GeneralDictionaryTotalEvidence206.Certificate (Yulang.GeneralNominalCenteredHeadAllocEncoding.registry value)
        state.core model focus key current.packet.children witness ∧
      witness.input = historical.input
Yulang.GeneralDictionaryDefaultRetainedCenter210.evidence_instance {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalCenteredHeadMatStepJournal.State roles}
  {current historical : Yulang.GeneralNominalCenters.Plan roles}
  {value : (Yulang.GeneralNominalCenteredHeadMatStepLocal.vocabulary roles).Registry}
  {root : (Yulang.GeneralNominalCenteredHeadMatStepLocal.vocabulary roles).Demand}
  {focus : Yulang.GeneralSourceDictionaries.Occurrence roles} {key : Nat}
  {model : Yulang.GeneralNominalCommonBridge.Assignment}
  (checked : (Yulang.GeneralDictionaryDefaultBoundary208.boundary roles).Checked value)
  (reachable : Yulang.B4TargetV7.Reachable (Yulang.GeneralDictionaryDefaultBoundary208.boundary roles) value root state)
  (frame :
    Yulang.GeneralNominalCenteredHeadOutputs.Frame (Yulang.GeneralNominalCenteredHeadAllocEncoding.registry value)
      state.core focus key current)
  (member : historical ∈ state.core.plans) (keyEq : historical.packet.declaration.id = key)
  (occurrence : historical.packet.site.occurrence = focus)
  (report :
    Yulang.GeneralNominalReportErasure.erase current.packet.context.state
        (Yulang.GeneralNominalPacketSupport.report current.packet) =
      Yulang.GeneralNominalReportErasure.erase historical.packet.context.state
        (Yulang.GeneralNominalPacketSupport.report historical.packet))
  (valid : Yulang.GeneralNominalCenteredHeadMatStepJournal.Models state model) :
  Yulang.GeneralDictionaryTotalEvidence206.Instance (Yulang.GeneralNominalCenteredHeadAllocEncoding.registry value)
    state.core model focus key current.packet.children
Yulang.GeneralDictionaryDefaultRevisionEquivalence210.inverse_result {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalCenteredHeadMatStepJournal.State roles}
  (revision : Yulang.GeneralNominalReobservationSteps.Revision state.core.erased.current) :
  Yulang.GeneralNominalCenteredHeadMatStepJournal.change
      (Yulang.GeneralNominalCenteredHeadMatStepJournal.change state revision.result)
      (Yulang.GeneralDictionaryDefaultRevisionEquivalence210.inverse revision).result =
    state
Yulang.GeneralDictionaryDefaultRevisionEquivalence210.structural_iff {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalCenteredHeadMatStepJournal.State roles} {registry : Yulang.GeneralDeclarations.Registry}
  (revision : Yulang.GeneralNominalReobservationSteps.Revision state.core.erased.current) :
  Yulang.GeneralDictionaryDefaultRevisionEvidence210.Structural registry
      (Yulang.GeneralNominalCenteredHeadMatStepJournal.change state revision.result).core.erased.current.context ↔
    Yulang.GeneralDictionaryDefaultRevisionEvidence210.Structural registry state.core.erased.current.context
Yulang.GeneralDictionaryDefaultRevisionEquivalence210.instance_iff {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalCenteredHeadMatStepJournal.State roles} {registry : Yulang.GeneralDeclarations.Registry}
  {model : Yulang.GeneralNominalCommonBridge.Assignment} {focus : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {key : Nat} {children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)}
  (revision : Yulang.GeneralNominalReobservationSteps.Revision state.core.erased.current)
  (shape : Yulang.GeneralDictionaryDefaultRevisionEvidence210.Structural registry state.core.erased.current.context)
  (before : Yulang.GeneralNominalCenteredHeadMatStepJournal.Models state model)
  (after :
    Yulang.GeneralNominalCenteredHeadMatStepJournal.Models
      (Yulang.GeneralNominalCenteredHeadMatStepJournal.change state revision.result) model) :
  Yulang.GeneralDictionaryTotalEvidence206.Instance registry
      (Yulang.GeneralNominalCenteredHeadMatStepJournal.change state revision.result).core model focus key children ↔
    Yulang.GeneralDictionaryTotalEvidence206.Instance registry state.core model focus key children
Yulang.GeneralDictionaryDefaultRevisionEquivalence210.evidence_iff {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalCenteredHeadMatStepJournal.State roles} {registry : Yulang.GeneralDeclarations.Registry}
  {model : Yulang.GeneralNominalCommonBridge.Assignment} {focus : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {payload : Yulang.GeneralDictionaryReadback.Payload}
  (revision : Yulang.GeneralNominalReobservationSteps.Revision state.core.erased.current)
  (shape : Yulang.GeneralDictionaryDefaultRevisionEvidence210.Structural registry state.core.erased.current.context)
  (before : Yulang.GeneralNominalCenteredHeadMatStepJournal.Models state model)
  (after :
    Yulang.GeneralNominalCenteredHeadMatStepJournal.Models
      (Yulang.GeneralNominalCenteredHeadMatStepJournal.change state revision.result) model) :
  Yulang.GeneralDictionaryTotalEvidence206.Evidence registry
      (Yulang.GeneralNominalCenteredHeadMatStepJournal.change state revision.result).core model focus payload ↔
    Yulang.GeneralDictionaryTotalEvidence206.Evidence registry state.core model focus payload
Yulang.GeneralDictionaryDefaultRevisionEquivalence210.certified_evidence_iff {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalCenteredHeadMatStepJournal.State roles} {registry : Yulang.GeneralDeclarations.Registry}
  {model : Yulang.GeneralNominalCommonBridge.Assignment} {focus : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {payload : Yulang.GeneralDictionaryReadback.Payload}
  (revision : Yulang.GeneralNominalReobservationSteps.Revision state.core.erased.current)
  (certificate : Yulang.GeneralNominalCenteredHeadMatStepRefresh.Reobserve state revision)
  (shape : Yulang.GeneralDictionaryDefaultRevisionEvidence210.Structural registry state.core.erased.current.context)
  (valid : Yulang.GeneralNominalCenteredHeadMatStepJournal.Models state model) :
  Yulang.GeneralDictionaryTotalEvidence206.Evidence registry
      (Yulang.GeneralNominalCenteredHeadMatStepJournal.change state revision.result).core model focus payload ↔
    Yulang.GeneralDictionaryTotalEvidence206.Evidence registry state.core model focus payload
Yulang.GeneralDictionaryDefaultRevisionEvidence210.certificate {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalCenteredHeadMatStepJournal.State roles}
  {historical : Yulang.GeneralNominalCenters.Plan roles} {registry : Yulang.GeneralDeclarations.Registry}
  {model : Yulang.GeneralNominalCommonBridge.Assignment} {focus : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {key : Nat} {children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)}
  (revision : Yulang.GeneralNominalReobservationSteps.Revision state.core.erased.current)
  (old : Yulang.GeneralDictionaryTotalEvidence206.Certificate registry state.core model focus key children historical)
  (shape :
    ∀ (query : Yulang.GeneralNominalInspection.Query),
      query ∈
          Yulang.GeneralNominalInspection.queries historical.packet.context.state
            historical.packet.context.interpretation historical.packet.declaration →
        Yulang.GeneralDictionaryDefaultStructuralReobserve210.Syntax query)
  (valid :
    Yulang.GeneralNominalCenteredHeadMatStepJournal.Models
      (Yulang.GeneralNominalCenteredHeadMatStepJournal.change state revision.result) model) :
  ∃ witness,
    Yulang.GeneralDictionaryTotalEvidence206.Certificate registry
        (Yulang.GeneralNominalCenteredHeadMatStepJournal.change state revision.result).core model focus key children
        witness ∧
      witness.input = historical.input
Yulang.GeneralDictionaryDefaultRevisionEvidence210.evidence_instance {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalCenteredHeadMatStepJournal.State roles} {registry : Yulang.GeneralDeclarations.Registry}
  {model : Yulang.GeneralNominalCommonBridge.Assignment} {focus : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {key : Nat} {children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)}
  (revision : Yulang.GeneralNominalReobservationSteps.Revision state.core.erased.current)
  (shape : Yulang.GeneralDictionaryDefaultRevisionEvidence210.Structural registry state.core.erased.current.context)
  (valid :
    Yulang.GeneralNominalCenteredHeadMatStepJournal.Models
      (Yulang.GeneralNominalCenteredHeadMatStepJournal.change state revision.result) model)
  (old : Yulang.GeneralDictionaryTotalEvidence206.Instance registry state.core model focus key children) :
  Yulang.GeneralDictionaryTotalEvidence206.Instance registry
    (Yulang.GeneralNominalCenteredHeadMatStepJournal.change state revision.result).core model focus key children
Yulang.GeneralDictionaryDefaultRevisionEvidence210.evidence {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalCenteredHeadMatStepJournal.State roles} {registry : Yulang.GeneralDeclarations.Registry}
  {model : Yulang.GeneralNominalCommonBridge.Assignment} {focus : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {payload : Yulang.GeneralDictionaryReadback.Payload}
  (revision : Yulang.GeneralNominalReobservationSteps.Revision state.core.erased.current)
  (shape : Yulang.GeneralDictionaryDefaultRevisionEvidence210.Structural registry state.core.erased.current.context)
  (valid :
    Yulang.GeneralNominalCenteredHeadMatStepJournal.Models
      (Yulang.GeneralNominalCenteredHeadMatStepJournal.change state revision.result) model)
  (old : Yulang.GeneralDictionaryTotalEvidence206.Evidence registry state.core model focus payload) :
  Yulang.GeneralDictionaryTotalEvidence206.Evidence registry
    (Yulang.GeneralNominalCenteredHeadMatStepJournal.change state revision.result).core model focus payload
Yulang.GeneralDictionaryDefaultRevisionFrames210.frame_finished {registry : Yulang.GeneralDeclarations.Registry}
  {roles✝ : Yulang.Roles.RoleDecls} {core : Yulang.GeneralNominalCenteredSteps.State roles✝}
  {focus : Yulang.GeneralSourceDictionaries.Occurrence roles✝} {key : Nat}
  {plan : Yulang.GeneralNominalCenters.Plan roles✝}
  (frame : Yulang.GeneralNominalCenteredHeadOutputs.Frame registry core focus key plan) :
  Yulang.GeneralNominalRecursiveInspection.Finished
    (Yulang.GeneralNominalRecursiveCandidates.report plan.packet.context plan.packet.declaration plan.packet.bounds)
Yulang.GeneralDictionaryDefaultRevisionFrames210.report {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalCenteredHeadMatStepJournal.State roles}
  {current historical : Yulang.GeneralNominalCenters.Plan roles} {registry : Yulang.GeneralDeclarations.Registry}
  {focus : Yulang.GeneralSourceDictionaries.Occurrence roles} {key : Nat}
  (checked : Yulang.GeneralDeclarations.Checked registry)
  (revision : Yulang.GeneralNominalReobservationSteps.Revision state.core.erased.current)
  (oldFrame : Yulang.GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key historical)
  (newFrame :
    Yulang.GeneralNominalCenteredHeadOutputs.Frame registry
      (Yulang.GeneralNominalCenteredHeadMatStepJournal.change state revision.result).core focus key current)
  (shape :
    ∀ (query : Yulang.GeneralNominalInspection.Query),
      query ∈
          Yulang.GeneralNominalInspection.queries historical.packet.context.state
            historical.packet.context.interpretation historical.packet.declaration →
        Yulang.GeneralDictionaryDefaultStructuralReobserve210.Syntax query) :
  Yulang.GeneralNominalReportErasure.erase current.packet.context.state
      (Yulang.GeneralNominalPacketSupport.report current.packet) =
    Yulang.GeneralNominalReportErasure.erase historical.packet.context.state
      (Yulang.GeneralNominalPacketSupport.report historical.packet)
Yulang.GeneralDictionaryDefaultRevisionFrames210.retained_data {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalCenteredHeadMatStepJournal.State roles}
  {current historical : Yulang.GeneralNominalCenters.Plan roles} {registry : Yulang.GeneralDeclarations.Registry}
  {focus : Yulang.GeneralSourceDictionaries.Occurrence roles} {key : Nat}
  (checked : Yulang.GeneralDeclarations.Checked registry)
  (revision : Yulang.GeneralNominalReobservationSteps.Revision state.core.erased.current)
  (oldFrame : Yulang.GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key historical)
  (newFrame :
    Yulang.GeneralNominalCenteredHeadOutputs.Frame registry
      (Yulang.GeneralNominalCenteredHeadMatStepJournal.change state revision.result).core focus key current)
  (shape :
    ∀ (query : Yulang.GeneralNominalInspection.Query),
      query ∈
          Yulang.GeneralNominalInspection.queries historical.packet.context.state
            historical.packet.context.interpretation historical.packet.declaration →
        Yulang.GeneralDictionaryDefaultStructuralReobserve210.Syntax query)
  (same : historical.input.occurrence = current.packet.site.occurrence) :
  Yulang.GeneralNominalCenteredHeadMatPlanData.Same
    (Yulang.GeneralDictionaryDefaultSemanticReplay209.recenter current historical.input same) historical
Yulang.GeneralDictionaryDefaultRevisionFrames210.certificate {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalCenteredHeadMatStepJournal.State roles}
  {current historical : Yulang.GeneralNominalCenters.Plan roles} {registry : Yulang.GeneralDeclarations.Registry}
  {focus : Yulang.GeneralSourceDictionaries.Occurrence roles} {key : Nat}
  {model : Yulang.GeneralNominalCommonBridge.Assignment}
  {children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)}
  (checked : Yulang.GeneralDeclarations.Checked registry)
  (revision : Yulang.GeneralNominalReobservationSteps.Revision state.core.erased.current)
  (newFrame :
    Yulang.GeneralNominalCenteredHeadOutputs.Frame registry
      (Yulang.GeneralNominalCenteredHeadMatStepJournal.change state revision.result).core focus key current)
  (old : Yulang.GeneralDictionaryTotalEvidence206.Certificate registry state.core model focus key children historical)
  (shape :
    ∀ (query : Yulang.GeneralNominalInspection.Query),
      query ∈
          Yulang.GeneralNominalInspection.queries historical.packet.context.state
            historical.packet.context.interpretation historical.packet.declaration →
        Yulang.GeneralDictionaryDefaultStructuralReobserve210.Syntax query)
  (valid :
    Yulang.GeneralNominalCenteredHeadMatStepJournal.Models
      (Yulang.GeneralNominalCenteredHeadMatStepJournal.change state revision.result) model) :
  ∃ witness,
    Yulang.GeneralDictionaryTotalEvidence206.Certificate registry
        (Yulang.GeneralNominalCenteredHeadMatStepJournal.change state revision.result).core model focus key children
        witness ∧
      witness.input = historical.input
Yulang.GeneralDictionaryDefaultRevisionFrames210.children {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalCenteredHeadMatStepJournal.State roles}
  {current historical : Yulang.GeneralNominalCenters.Plan roles} {registry : Yulang.GeneralDeclarations.Registry}
  {focus : Yulang.GeneralSourceDictionaries.Occurrence roles} {key : Nat}
  (checked : Yulang.GeneralDeclarations.Checked registry)
  (revision : Yulang.GeneralNominalReobservationSteps.Revision state.core.erased.current)
  (oldFrame : Yulang.GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key historical)
  (newFrame :
    Yulang.GeneralNominalCenteredHeadOutputs.Frame registry
      (Yulang.GeneralNominalCenteredHeadMatStepJournal.change state revision.result).core focus key current)
  (shape :
    ∀ (query : Yulang.GeneralNominalInspection.Query),
      query ∈
          Yulang.GeneralNominalInspection.queries historical.packet.context.state
            historical.packet.context.interpretation historical.packet.declaration →
        Yulang.GeneralDictionaryDefaultStructuralReobserve210.Syntax query) :
  current.packet.children = historical.packet.children
Yulang.GeneralDictionaryDefaultStructuralReobserve210.traced {roles✝ : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalSaturationState.State roles✝} {query : Yulang.GeneralNominalInspection.Query}
  {bounds : Yulang.GeneralNominalInspection.Bounds state.context.state}
  {origin : Option Yulang.GeneralNominalRecursiveInspection.Origin}
  (revision : Yulang.GeneralNominalReobservationSteps.Revision state)
  (shape : Yulang.GeneralDictionaryDefaultStructuralReobserve210.Syntax query)
  (finished :
    Yulang.GeneralNominalRecursiveInspection.Finished
      (Yulang.GeneralNominalRecursiveInspection.inspect state.context.state query bounds origin)) :
  Yulang.GeneralNominalInspectionTrace197.Trace state.context.state
    (Yulang.GeneralDictionaryDefaultStructuralReobserve210.view revision) query bounds
Yulang.GeneralDictionaryDefaultStructuralReobserve210.tracedMany {roles✝ : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalSaturationState.State roles✝} {queries : List Yulang.GeneralNominalInspection.Query}
  {bounds : List (Yulang.GeneralNominalInspection.Bounds state.context.state)}
  {origins : Nat → Option Yulang.GeneralNominalRecursiveInspection.Origin} {index : Nat}
  (revision : Yulang.GeneralNominalReobservationSteps.Revision state)
  (shape :
    ∀ (query : Yulang.GeneralNominalInspection.Query),
      query ∈ queries → Yulang.GeneralDictionaryDefaultStructuralReobserve210.Syntax query)
  (finished :
    Yulang.GeneralNominalRecursiveInspection.Finished
      (Yulang.GeneralNominalRecursiveInspection.inspectMany state.context.state queries bounds origins index)) :
  Yulang.GeneralNominalInspectionTrace197.Traces state.context.state
    (Yulang.GeneralDictionaryDefaultStructuralReobserve210.view revision) queries bounds
Yulang.GeneralDictionaryDefaultStructuralReobserve210.candidate_rechecked {roles✝ : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalSaturationState.State roles✝} {declaration : Yulang.GeneralDeclarations.Declaration}
  {bounds : List (Yulang.GeneralNominalInspection.Bounds state.context.state)}
  (revision : Yulang.GeneralNominalReobservationSteps.Revision state)
  (shape :
    ∀ (query : Yulang.GeneralNominalInspection.Query),
      query ∈ Yulang.GeneralNominalInspection.queries state.context.state state.context.interpretation declaration →
        Yulang.GeneralDictionaryDefaultStructuralReobserve210.Syntax query)
  (finished :
    Yulang.GeneralNominalRecursiveInspection.Finished
      (Yulang.GeneralNominalRecursiveInspection.inspectMany state.context.state
        (Yulang.GeneralNominalInspection.queries state.context.state state.context.interpretation declaration) bounds
        (fun x => none) 0)) :
  Yulang.GeneralNominalViewTransport196.Rechecked state.context
    (Yulang.GeneralDictionaryDefaultStructuralReobserve210.view revision) declaration bounds
Yulang.GeneralDictionaryDefaultStructuralReobserve210.candidate_report {roles✝ : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalSaturationState.State roles✝} {declaration : Yulang.GeneralDeclarations.Declaration}
  {bounds : List (Yulang.GeneralNominalInspection.Bounds state.context.state)}
  (revision : Yulang.GeneralNominalReobservationSteps.Revision state)
  (shape :
    ∀ (query : Yulang.GeneralNominalInspection.Query),
      query ∈ Yulang.GeneralNominalInspection.queries state.context.state state.context.interpretation declaration →
        Yulang.GeneralDictionaryDefaultStructuralReobserve210.Syntax query)
  (finished :
    Yulang.GeneralNominalRecursiveInspection.Finished
      (Yulang.GeneralNominalRecursiveCandidates.report state.context declaration bounds)) :
  Yulang.GeneralNominalReportErasure.erase revision.snapshot
      (Yulang.GeneralNominalRecursiveCandidates.report
        { state := revision.snapshot, interpretation := state.context.interpretation } declaration bounds) =
    Yulang.GeneralNominalReportErasure.erase state.context.state
      (Yulang.GeneralNominalRecursiveCandidates.report state.context declaration bounds)
Yulang.GeneralDictionaryDefaultActualHead210.head_schema {roles : Yulang.Roles.RoleDecls}
  {first last : Yulang.GeneralNominalCenters.Plan roles}
  (queries :
    Yulang.GeneralNominalInspection.queries first.packet.context.state first.packet.context.interpretation
        first.packet.declaration =
      Yulang.GeneralNominalInspection.queries last.packet.context.state last.packet.context.interpretation
        last.packet.declaration)
  (input : first.input = last.input) : first.headSchema = last.headSchema
Yulang.GeneralDictionaryDefaultActualHead210.head_holds {roles : Yulang.Roles.RoleDecls}
  {first last : Yulang.GeneralNominalCenters.Plan roles} {model : Yulang.GeneralNominalCommonBridge.Assignment}
  (queries :
    Yulang.GeneralNominalInspection.queries first.packet.context.state first.packet.context.interpretation
        first.packet.declaration =
      Yulang.GeneralNominalInspection.queries last.packet.context.state last.packet.context.interpretation
        last.packet.declaration)
  (input : first.input = last.input) (names : ∀ (name : Nat), first.binder name = last.binder name) :
  first.SchemaHolds first.headSchema model ↔ last.SchemaHolds last.headSchema model
Yulang.GeneralDictionaryDefaultActualHead210.terminal_replay {roles : Yulang.Roles.RoleDecls}
  {first last : Yulang.GeneralNominalCenters.Plan roles} {model : Yulang.GeneralNominalCommonBridge.Assignment}
  (declaration : first.packet.declaration = last.packet.declaration)
  (occurrence : first.packet.site.occurrence = last.packet.site.occurrence)
  (constructors : first.packet.registry.constructors = last.packet.registry.constructors)
  (interpretation : first.packet.context.interpretation = last.packet.context.interpretation)
  (queries :
    Yulang.GeneralNominalInspection.queries first.packet.context.state first.packet.context.interpretation
        first.packet.declaration =
      Yulang.GeneralNominalInspection.queries last.packet.context.state last.packet.context.interpretation
        last.packet.declaration)
  (input : first.input = last.input) (names : ∀ (name : Nat), first.binder name = last.binder name)
  (terminal : first.packet.declaration.requirements = [])
  (old : Yulang.GeneralNominalCenteredHeadMatStepPackets.Holds first model)
  (current : Yulang.GeneralNominalState.Models last.packet.context.state model)
  (ordinary : Yulang.GeneralNominalPacketSupport.Ordinary last.packet model)
  (projections :
    Yulang.GeneralNominalRecursiveInspection.ProjectionModels last.packet.context.state
      (Yulang.GeneralNominalPacketSupport.report last.packet) model)
  (fits :
    ∀ (name : Nat),
      name ∈ last.packet.declaration.inputNames ∨ Yulang.GeneralNominalSharedCaptures.Needed last.packet name →
        Yulang.GeneralNominalCaptureMerges.Fits model
          ((Yulang.GeneralNominalPacketSupport.capture last.packet).inputs name) (model (last.binder name)).fst) :
  Yulang.GeneralNominalCenteredHeadMatStepPackets.Holds last model
Yulang.GeneralDictionaryDefaultBinderShape210.output_name {roles : Yulang.Roles.RoleDecls}
  {first last : Yulang.GeneralNominalCenters.Plan roles} {name : Nat}
  (seed : first.packet.context.state.seed = last.packet.context.state.seed)
  (identity : first.packet.site.occurrence.identity = last.packet.site.occurrence.identity)
  (declaration : first.packet.declaration = last.packet.declaration)
  (output : name ∈ first.packet.declaration.outputNames) : first.binder name = last.binder name
Yulang.GeneralDictionaryDefaultBinderShape210.input_name {roles : Yulang.Roles.RoleDecls}
  {first last : Yulang.GeneralNominalCenters.Plan roles} {name : Nat}
  (seed : first.packet.context.state.seed = last.packet.context.state.seed)
  (identity : first.packet.site.occurrence.identity = last.packet.site.occurrence.identity)
  (declaration : first.packet.declaration = last.packet.declaration)
  (input : ¬name ∈ first.packet.declaration.outputNames)
  (shape : Yulang.GeneralDictionaryDefaultBinderShape210.InputShape first last name) :
  first.binder name = last.binder name
Yulang.GeneralDictionaryDefaultBinderShape210.names {roles : Yulang.Roles.RoleDecls}
  {first last : Yulang.GeneralNominalCenters.Plan roles}
  (seed : first.packet.context.state.seed = last.packet.context.state.seed)
  (identity : first.packet.site.occurrence.identity = last.packet.site.occurrence.identity)
  (declaration : first.packet.declaration = last.packet.declaration)
  (shape :
    ∀ (name : Nat),
      ¬name ∈ first.packet.declaration.outputNames →
        Yulang.GeneralDictionaryDefaultBinderShape210.InputShape first last name)
  (name : Nat) : first.binder name = last.binder name
Yulang.GeneralDictionaryDefaultBinderShape210.body_iff {roles : Yulang.Roles.RoleDecls}
  {first last : Yulang.GeneralNominalCenters.Plan roles} {model : Yulang.GeneralNominalCommonBridge.Assignment}
  {target : Nat} {body : Yulang.GeneralDictionaryAssociatedProvenance.Body}
  (seed : first.packet.context.state.seed = last.packet.context.state.seed)
  (identity : first.packet.site.occurrence.identity = last.packet.site.occurrence.identity)
  (declaration : first.packet.declaration = last.packet.declaration)
  (constructors : first.packet.registry.constructors = last.packet.registry.constructors)
  (interpretation : first.packet.context.interpretation = last.packet.context.interpretation)
  (input : first.input = last.input)
  (shape :
    ∀ (name : Nat),
      ¬name ∈ first.packet.declaration.outputNames →
        Yulang.GeneralDictionaryDefaultBinderShape210.InputShape first last name) :
  Yulang.GeneralNominalCenteredHeadMatEffects.BodyHolds first target model body ↔
    Yulang.GeneralNominalCenteredHeadMatEffects.BodyHolds last target model body
Yulang.GeneralDictionaryDefaultCollapseExpression210.fits_unique {model : Yulang.GeneralNominalCommonBridge.Assignment}
  {first last : Yulang.GeneralSourceState.Interval} {a b : Yulang.CommonNominalFullCarrier.Ty}
  (lower : Yulang.CommonNominalFullCarrier.Equivalent (model first.fst).fst (model last.fst).fst)
  (upper : Yulang.CommonNominalFullCarrier.Equivalent (model first.snd).fst (model last.snd).fst)
  (point : Yulang.CommonNominalFullCarrier.Equivalent (model last.fst).fst (model last.snd).fst)
  (fa : Yulang.GeneralNominalCaptureMerges.Fits model first a)
  (fb : Yulang.GeneralNominalCaptureMerges.Fits model last b) : Yulang.CommonNominalFullCarrier.Equivalent a b
Yulang.GeneralDictionaryDefaultCollapseExpression210.actual_equivalent {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalSaturationState.State roles}
  {revision : Yulang.GeneralNominalReobservationSteps.Revision state}
  (s : Yulang.GeneralDictionarySemanticCollapse.Shape revision) (registry : Yulang.GeneralDeclarations.Registry)
  (invocation : Nat) (declaration : Yulang.GeneralDeclarations.Declaration)
  (model : Yulang.GeneralNominalCommonBridge.Assignment) (declared : s.binder ∈ declaration.inputNames)
  (old :
    Yulang.GeneralNominalRecursiveInspection.ProjectionModels state.context.state
      (Yulang.GeneralNominalRecursiveInspection.inspect state.context.state
        (Yulang.GeneralDictionarySemanticCollapse.query s) (s.root, s.root) none)
      model)
  (firstPoint : s.first.fst = s.first.snd) (lastPoint : s.last.fst = s.last.snd)
  (propagated :
    Yulang.GeneralNominalState.Models
      (Yulang.GeneralNominalAllocation.propagate state.context.state registry invocation declaration
        (Yulang.GeneralNominalRecursiveInspection.bindings state.context.state
          (Yulang.GeneralNominalRecursiveInspection.inspect state.context.state
            (Yulang.GeneralDictionarySemanticCollapse.query s) (s.root, s.root) none)))
      model)
  (before after : Yulang.CommonNominalFullCarrier.Ty)
  (oldFits :
    Yulang.GeneralNominalCaptureMerges.Fits model
      ((Yulang.GeneralDictionarySemanticCollapseSchema.oldCapture s registry invocation declaration).inputs s.binder)
      before)
  (newFits :
    Yulang.GeneralNominalCaptureMerges.Fits model
      ((Yulang.GeneralDictionarySemanticCollapseSchema.newCapture s registry invocation declaration).inputs s.binder)
      after) :
  Yulang.CommonNominalFullCarrier.Equivalent before after
Yulang.GeneralDictionaryDefaultCollapseExpression210.expression_equivalent {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalSaturationState.State roles}
  {revision : Yulang.GeneralNominalReobservationSteps.Revision state}
  (s : Yulang.GeneralDictionarySemanticCollapse.Shape revision) (registry : Yulang.GeneralDeclarations.Registry)
  (invocation : Nat) (declaration : Yulang.GeneralDeclarations.Declaration)
  (model : Yulang.GeneralNominalCommonBridge.Assignment) (declared : s.binder ∈ declaration.inputNames)
  (old :
    Yulang.GeneralNominalRecursiveInspection.ProjectionModels state.context.state
      (Yulang.GeneralNominalRecursiveInspection.inspect state.context.state
        (Yulang.GeneralDictionarySemanticCollapse.query s) (s.root, s.root) none)
      model)
  (firstPoint : s.first.fst = s.first.snd) (lastPoint : s.last.fst = s.last.snd)
  (propagated :
    Yulang.GeneralNominalState.Models
      (Yulang.GeneralNominalAllocation.propagate state.context.state registry invocation declaration
        (Yulang.GeneralNominalRecursiveInspection.bindings state.context.state
          (Yulang.GeneralNominalRecursiveInspection.inspect state.context.state
            (Yulang.GeneralDictionarySemanticCollapse.query s) (s.root, s.root) none)))
      model)
  (before after : Yulang.GeneralNominalMaterialization.Mode → Nat → Yulang.CommonNominalFullCarrier.Ty)
  (oldFits :
    Yulang.GeneralNominalCaptureMerges.Fits model
      ((Yulang.GeneralDictionarySemanticCollapseSchema.oldCapture s registry invocation declaration).inputs s.binder)
      (before Yulang.GeneralNominalMaterialization.Mode.actual s.binder))
  (newFits :
    Yulang.GeneralNominalCaptureMerges.Fits model
      ((Yulang.GeneralDictionarySemanticCollapseSchema.newCapture s registry invocation declaration).inputs s.binder)
      (after Yulang.GeneralNominalMaterialization.Mode.actual s.binder))
  (expression : Yulang.GeneralNominalCenteredHeadMatExpressions.Expr)
  (scope : ∀ (name : Nat), name ∈ Yulang.GeneralNominalCenteredHeadMatExtension.names expression → name = s.binder) :
  Yulang.CommonNominalFullCarrier.Equivalent
    (Yulang.GeneralNominalCenteredHeadMatExpressions.value before Yulang.GeneralNominalMaterialization.Mode.actual
      expression)
    (Yulang.GeneralNominalCenteredHeadMatExpressions.value after Yulang.GeneralNominalMaterialization.Mode.actual
      expression)
Yulang.GeneralDictionaryDefaultCollapseRegression210.expression_scope (name : Nat) :
  name ∈
      Yulang.GeneralNominalCenteredHeadMatExtension.names
        Yulang.GeneralDictionaryDefaultCollapseRegression210.expression →
    name = Yulang.GeneralDictionarySemanticCollapseExample.shape.binder
Yulang.GeneralDictionaryDefaultCollapseRegression210.old_fits :
  Yulang.GeneralNominalCaptureMerges.Fits Yulang.GeneralDictionarySemanticCollapseExample.model
    ((Yulang.GeneralDictionarySemanticCollapseSchema.oldCapture Yulang.GeneralDictionarySemanticCollapseExample.shape
          Yulang.GeneralDictionarySemanticCollapseOutputExample.registry
          Yulang.GeneralDictionarySemanticCollapseOutputExample.outputRoot.identity
          Yulang.GeneralDictionarySemanticCollapseOutputExample.declaration).inputs
      7)
    (Yulang.GeneralDictionaryDefaultCollapseRegression210.before Yulang.GeneralNominalMaterialization.Mode.actual 7)
Yulang.GeneralDictionaryDefaultCollapseRegression210.new_fits :
  Yulang.GeneralNominalCaptureMerges.Fits Yulang.GeneralDictionarySemanticCollapseExample.model
    ((Yulang.GeneralDictionarySemanticCollapseSchema.newCapture Yulang.GeneralDictionarySemanticCollapseExample.shape
          Yulang.GeneralDictionarySemanticCollapseOutputExample.registry
          Yulang.GeneralDictionarySemanticCollapseOutputExample.outputRoot.identity
          Yulang.GeneralDictionarySemanticCollapseOutputExample.declaration).inputs
      7)
    (Yulang.GeneralDictionaryDefaultCollapseRegression210.after Yulang.GeneralNominalMaterialization.Mode.actual 7)
Yulang.GeneralDictionaryDefaultCollapseRegression210.transported :
  Yulang.CommonNominalFullCarrier.Equivalent
    (Yulang.GeneralNominalCenteredHeadMatExpressions.value Yulang.GeneralDictionaryDefaultCollapseRegression210.before
      Yulang.GeneralNominalMaterialization.Mode.actual Yulang.GeneralDictionaryDefaultCollapseRegression210.expression)
    (Yulang.GeneralNominalCenteredHeadMatExpressions.value Yulang.GeneralDictionaryDefaultCollapseRegression210.after
      Yulang.GeneralNominalMaterialization.Mode.actual Yulang.GeneralDictionaryDefaultCollapseRegression210.expression)
Yulang.GeneralDictionaryDefaultCollapseRegression210.source_ids_changed :
  (Yulang.GeneralDictionarySemanticCollapseSchema.oldCapture Yulang.GeneralDictionarySemanticCollapseExample.shape
          Yulang.GeneralDictionarySemanticCollapseOutputExample.registry
          Yulang.GeneralDictionarySemanticCollapseOutputExample.outputRoot.identity
          Yulang.GeneralDictionarySemanticCollapseOutputExample.declaration).inputs
      7 ≠
    (Yulang.GeneralDictionarySemanticCollapseSchema.newCapture Yulang.GeneralDictionarySemanticCollapseExample.shape
          Yulang.GeneralDictionarySemanticCollapseOutputExample.registry
          Yulang.GeneralDictionarySemanticCollapseOutputExample.outputRoot.identity
          Yulang.GeneralDictionarySemanticCollapseOutputExample.declaration).inputs
      7
Yulang.GeneralDictionaryDefaultNonpointCertificate210.certificate {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalSaturationState.State roles}
  {revision : Yulang.GeneralNominalReobservationSteps.Revision state}
  {oldState : Yulang.GeneralNominalCenteredSteps.State roles}
  {focus : Yulang.GeneralSourceDictionaries.Occurrence roles} {key : Nat}
  {children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)}
  {newState : Yulang.GeneralNominalCenteredSteps.State roles}
  (s : Yulang.GeneralDictionarySemanticCollapse.Shape revision) (registry : Yulang.GeneralDeclarations.Registry)
  (site : Yulang.GeneralNominalDemandMerging.Site roles) (declaration : Yulang.GeneralDeclarations.Declaration)
  (checked : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration)
  (center : Yulang.GeneralNominalCenters.Site roles) (same : center.occurrence = site.occurrence)
  (queries :
    Yulang.GeneralNominalInspection.queries state.context.state state.context.interpretation declaration =
      [Yulang.GeneralDictionarySemanticCollapse.query s])
  (names : declaration.inputNames = [s.binder]) (terminal : declaration.requirements = [])
  (nonpoint :
    (Yulang.GeneralDictionarySemanticCollapseAllocation.firstPair s).fst ≠
      (Yulang.GeneralDictionarySemanticCollapseAllocation.firstPair s).snd)
  (model : Yulang.GeneralNominalCommonBridge.Assignment)
  (old :
    Yulang.GeneralDictionaryTotalEvidence206.Certificate registry oldState model focus key children
      (Yulang.GeneralDictionaryDefaultNonpointTerminal210.oldPlan s registry site declaration checked center same))
  (frame :
    Yulang.GeneralNominalCenteredHeadOutputs.Frame registry newState focus key
      (Yulang.GeneralDictionaryDefaultNonpointTerminal210.newPlan s registry site declaration checked center same))
  (current : Yulang.GeneralNominalState.Models revision.snapshot model) :
  Yulang.GeneralDictionaryTotalEvidence206.Certificate registry newState model focus key children
    (Yulang.GeneralDictionaryDefaultNonpointTerminal210.newPlan s registry site declaration checked center same)
Yulang.GeneralDictionaryDefaultNonpointCertificate210.leaf_evidence {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalSaturationState.State roles}
  {revision : Yulang.GeneralNominalReobservationSteps.Revision state}
  {oldState : Yulang.GeneralNominalCenteredSteps.State roles}
  {focus : Yulang.GeneralSourceDictionaries.Occurrence roles} {key : Nat}
  {newState : Yulang.GeneralNominalCenteredSteps.State roles}
  (s : Yulang.GeneralDictionarySemanticCollapse.Shape revision) (registry : Yulang.GeneralDeclarations.Registry)
  (site : Yulang.GeneralNominalDemandMerging.Site roles) (declaration : Yulang.GeneralDeclarations.Declaration)
  (checked : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration)
  (center : Yulang.GeneralNominalCenters.Site roles) (same : center.occurrence = site.occurrence)
  (queries :
    Yulang.GeneralNominalInspection.queries state.context.state state.context.interpretation declaration =
      [Yulang.GeneralDictionarySemanticCollapse.query s])
  (names : declaration.inputNames = [s.binder]) (terminal : declaration.requirements = [])
  (nonpoint :
    (Yulang.GeneralDictionarySemanticCollapseAllocation.firstPair s).fst ≠
      (Yulang.GeneralDictionarySemanticCollapseAllocation.firstPair s).snd)
  (model : Yulang.GeneralNominalCommonBridge.Assignment)
  (old :
    Yulang.GeneralDictionaryTotalEvidence206.Certificate registry oldState model focus key []
      (Yulang.GeneralDictionaryDefaultNonpointTerminal210.oldPlan s registry site declaration checked center same))
  (frame :
    Yulang.GeneralNominalCenteredHeadOutputs.Frame registry newState focus key
      (Yulang.GeneralDictionaryDefaultNonpointTerminal210.newPlan s registry site declaration checked center same))
  (current : Yulang.GeneralNominalState.Models revision.snapshot model) :
  Yulang.GeneralDictionaryTotalEvidence206.Evidence registry newState model focus
    (Yulang.CommonRoleOutermostResolver.Dictionary.node key [])
Yulang.GeneralDictionaryDefaultNonpointCollapse210.aggregate_nonpoint (state : Yulang.GeneralNominalState.State)
  (registry : Yulang.GeneralDeclarations.Registry) (root key name : Nat) :
  Yulang.GeneralNominalAllocation.source state registry root
      (Yulang.GeneralNominalAllocation.origin root key 0 name 0) ≠
    Yulang.GeneralNominalAllocation.source state registry root
      (Yulang.GeneralNominalAllocation.origin root key 1 name 0)
Yulang.GeneralDictionaryDefaultNonpointCollapse210.repeated_nonpoint (state : Yulang.GeneralNominalState.State)
  (registry : Yulang.GeneralDeclarations.Registry) (root key binder name : Nat)
  (a b : Yulang.GeneralSourceState.Interval) :
  ((Yulang.GeneralNominalAllocation.capture state registry root key [(binder, a), (binder, b)]).inputs name).fst ≠
    ((Yulang.GeneralNominalAllocation.capture state registry root key [(binder, a), (binder, b)]).inputs name).snd
Yulang.GeneralDictionaryDefaultNonpointCollapse210.retained_nonpoint (state : Yulang.GeneralNominalState.State)
  (registry : Yulang.GeneralDeclarations.Registry) (root key binder name : Nat) (a : Yulang.GeneralSourceState.Interval)
  (nonpoint : a.fst ≠ a.snd) :
  ((Yulang.GeneralNominalAllocation.capture state registry root key [(binder, a)]).inputs name).fst ≠
    ((Yulang.GeneralNominalAllocation.capture state registry root key [(binder, a)]).inputs name).snd
Yulang.GeneralDictionaryDefaultNonpointCollapse210.shape {roles : Yulang.Roles.RoleDecls}
  {first last : Yulang.GeneralNominalCenters.Plan roles} {binder : Nat} {a b : Yulang.GeneralSourceState.Interval}
  (before : first.packet.bindings = [(binder, a), (binder, b)]) (after : last.packet.bindings = [(binder, a)])
  (nonpoint : a.fst ≠ a.snd) (name : Nat) : Yulang.GeneralDictionaryDefaultBinderShape210.InputShape first last name
Yulang.GeneralDictionaryDefaultNonpointCollapse210.body_iff {roles : Yulang.Roles.RoleDecls}
  {first last : Yulang.GeneralNominalCenters.Plan roles} {model : Yulang.GeneralNominalCommonBridge.Assignment}
  {binder : Nat} {a b : Yulang.GeneralSourceState.Interval} {target : Nat}
  {body : Yulang.GeneralDictionaryAssociatedProvenance.Body}
  (seed : first.packet.context.state.seed = last.packet.context.state.seed)
  (identity : first.packet.site.occurrence.identity = last.packet.site.occurrence.identity)
  (declaration : first.packet.declaration = last.packet.declaration)
  (constructors : first.packet.registry.constructors = last.packet.registry.constructors)
  (interpretation : first.packet.context.interpretation = last.packet.context.interpretation)
  (input : first.input = last.input) (before : first.packet.bindings = [(binder, a), (binder, b)])
  (after : last.packet.bindings = [(binder, a)]) (nonpoint : a.fst ≠ a.snd) :
  Yulang.GeneralNominalCenteredHeadMatEffects.BodyHolds first target model body ↔
    Yulang.GeneralNominalCenteredHeadMatEffects.BodyHolds last target model body
Yulang.GeneralDictionaryDefaultNonpointTerminal210.replay {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalSaturationState.State roles}
  {revision : Yulang.GeneralNominalReobservationSteps.Revision state}
  (s : Yulang.GeneralDictionarySemanticCollapse.Shape revision) (registry : Yulang.GeneralDeclarations.Registry)
  (site : Yulang.GeneralNominalDemandMerging.Site roles) (declaration : Yulang.GeneralDeclarations.Declaration)
  (checked : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration)
  (center : Yulang.GeneralNominalCenters.Site roles) (same : center.occurrence = site.occurrence)
  (queries :
    Yulang.GeneralNominalInspection.queries state.context.state state.context.interpretation declaration =
      [Yulang.GeneralDictionarySemanticCollapse.query s])
  (names : declaration.inputNames = [s.binder]) (terminal : declaration.requirements = [])
  (nonpoint :
    (Yulang.GeneralDictionarySemanticCollapseAllocation.firstPair s).fst ≠
      (Yulang.GeneralDictionarySemanticCollapseAllocation.firstPair s).snd)
  (model : Yulang.GeneralNominalCommonBridge.Assignment)
  (old :
    Yulang.GeneralNominalCenteredHeadMatStepPackets.Holds
      (Yulang.GeneralDictionaryDefaultNonpointTerminal210.oldPlan s registry site declaration checked center same)
      model)
  (current : Yulang.GeneralNominalState.Models revision.snapshot model) :
  Yulang.GeneralNominalCenteredHeadMatStepPackets.Holds
    (Yulang.GeneralDictionaryDefaultNonpointTerminal210.newPlan s registry site declaration checked center same) model
Yulang.GeneralDictionaryDefaultRevisionTrace210.trans {roles✝ : Yulang.Roles.RoleDecls}
  {a b c : Yulang.GeneralNominalCenteredHeadMatStepJournal.State roles✝}
  (first : Yulang.GeneralDictionaryDefaultRevisionTrace210.Trace a b)
  (last : Yulang.GeneralDictionaryDefaultRevisionTrace210.Trace b c) :
  Yulang.GeneralDictionaryDefaultRevisionTrace210.Trace a c
Yulang.GeneralDictionaryDefaultRevisionTrace210.models {roles✝ : Yulang.Roles.RoleDecls}
  {first last : Yulang.GeneralNominalCenteredHeadMatStepJournal.State roles✝}
  {model : Yulang.GeneralNominalCommonBridge.Assignment}
  (trace : Yulang.GeneralDictionaryDefaultRevisionTrace210.Trace first last) :
  Yulang.GeneralNominalCenteredHeadMatStepJournal.Models last model ↔
    Yulang.GeneralNominalCenteredHeadMatStepJournal.Models first model
Yulang.GeneralDictionaryDefaultRevisionTrace210.structural {roles✝ : Yulang.Roles.RoleDecls}
  {first last : Yulang.GeneralNominalCenteredHeadMatStepJournal.State roles✝}
  {registry : Yulang.GeneralDeclarations.Registry}
  (trace : Yulang.GeneralDictionaryDefaultRevisionTrace210.Trace first last) :
  Yulang.GeneralDictionaryDefaultRevisionEvidence210.Structural registry last.core.erased.current.context ↔
    Yulang.GeneralDictionaryDefaultRevisionEvidence210.Structural registry first.core.erased.current.context
Yulang.GeneralDictionaryDefaultRevisionTrace210.instance_iff_trace {roles✝ : Yulang.Roles.RoleDecls}
  {first last : Yulang.GeneralNominalCenteredHeadMatStepJournal.State roles✝}
  {registry : Yulang.GeneralDeclarations.Registry} {model : Yulang.GeneralNominalCommonBridge.Assignment}
  {focus : Yulang.GeneralSourceDictionaries.Occurrence roles✝} {key : Nat}
  {children : List (Yulang.GeneralSourceDictionaries.Occurrence roles✝)}
  (trace : Yulang.GeneralDictionaryDefaultRevisionTrace210.Trace first last)
  (shape : Yulang.GeneralDictionaryDefaultRevisionEvidence210.Structural registry first.core.erased.current.context)
  (valid : Yulang.GeneralNominalCenteredHeadMatStepJournal.Models first model) :
  Yulang.GeneralDictionaryTotalEvidence206.Instance registry last.core model focus key children ↔
    Yulang.GeneralDictionaryTotalEvidence206.Instance registry first.core model focus key children
Yulang.GeneralDictionaryDefaultRevisionTrace210.evidence {roles✝ : Yulang.Roles.RoleDecls}
  {first last : Yulang.GeneralNominalCenteredHeadMatStepJournal.State roles✝}
  {registry : Yulang.GeneralDeclarations.Registry} {model : Yulang.GeneralNominalCommonBridge.Assignment}
  {focus : Yulang.GeneralSourceDictionaries.Occurrence roles✝} {payload : Yulang.GeneralDictionaryReadback.Payload}
  (trace : Yulang.GeneralDictionaryDefaultRevisionTrace210.Trace first last)
  (shape : Yulang.GeneralDictionaryDefaultRevisionEvidence210.Structural registry first.core.erased.current.context)
  (valid : Yulang.GeneralNominalCenteredHeadMatStepJournal.Models first model) :
  Yulang.GeneralDictionaryTotalEvidence206.Evidence registry last.core model focus payload ↔
    Yulang.GeneralDictionaryTotalEvidence206.Evidence registry first.core model focus payload
Yulang.GeneralDictionaryDefaultScopedRevision210.key_iff {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalCenteredHeadMatStepJournal.State roles} {registry : Yulang.GeneralDeclarations.Registry}
  {key : Nat} (revision : Yulang.GeneralNominalReobservationSteps.Revision state.core.erased.current) :
  Yulang.GeneralDictionaryDefaultScopedRevision210.StructuralKey registry
      (Yulang.GeneralNominalCenteredHeadMatStepJournal.change state revision.result).core.erased.current.context key ↔
    Yulang.GeneralDictionaryDefaultScopedRevision210.StructuralKey registry state.core.erased.current.context key
Yulang.GeneralDictionaryDefaultScopedRevision210.shaped_forward {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalCenteredHeadMatStepJournal.State roles} {registry : Yulang.GeneralDeclarations.Registry}
  {roles✝ : Yulang.Roles.RoleDecls} {tree : Yulang.GeneralSourceDictionaries.Dictionary roles✝}
  (revision : Yulang.GeneralNominalReobservationSteps.Revision state.core.erased.current)
  (shape : Yulang.GeneralDictionaryDefaultScopedRevision210.Shaped registry state.core.erased.current.context tree) :
  Yulang.GeneralDictionaryDefaultScopedRevision210.Shaped registry
    (Yulang.GeneralNominalCenteredHeadMatStepJournal.change state revision.result).core.erased.current.context tree
Yulang.GeneralDictionaryDefaultScopedRevision210.local_instance {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalCenteredHeadMatStepJournal.State roles} {registry : Yulang.GeneralDeclarations.Registry}
  {key : Nat} {model : Yulang.GeneralNominalCommonBridge.Assignment}
  {focus : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)}
  (revision : Yulang.GeneralNominalReobservationSteps.Revision state.core.erased.current)
  (shape :
    Yulang.GeneralDictionaryDefaultScopedRevision210.StructuralKey registry state.core.erased.current.context key)
  (valid :
    Yulang.GeneralNominalCenteredHeadMatStepJournal.Models
      (Yulang.GeneralNominalCenteredHeadMatStepJournal.change state revision.result) model)
  (old : Yulang.GeneralDictionaryTotalEvidence206.Instance registry state.core model focus key children) :
  Yulang.GeneralDictionaryTotalEvidence206.Instance registry
    (Yulang.GeneralNominalCenteredHeadMatStepJournal.change state revision.result).core model focus key children
Yulang.GeneralDictionaryDefaultScopedRevision210.indexed {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalCenteredHeadMatStepJournal.State roles}
  {model : Yulang.GeneralNominalCommonBridge.Assignment} {registry : Yulang.GeneralDeclarations.Registry}
  {tree : Yulang.GeneralSourceDictionaries.Dictionary roles}
  (revision : Yulang.GeneralNominalReobservationSteps.Revision state.core.erased.current)
  (valid :
    Yulang.GeneralNominalCenteredHeadMatStepJournal.Models
      (Yulang.GeneralNominalCenteredHeadMatStepJournal.change state revision.result) model)
  (old :
    Yulang.GeneralSourceDictionaries.Evidence
      (Yulang.GeneralDictionaryTotalEvidence206.Instance registry state.core model) tree)
  (shape : Yulang.GeneralDictionaryDefaultScopedRevision210.Shaped registry state.core.erased.current.context tree) :
  Yulang.GeneralSourceDictionaries.Evidence
    (Yulang.GeneralDictionaryTotalEvidence206.Instance registry
      (Yulang.GeneralNominalCenteredHeadMatStepJournal.change state revision.result).core model)
    tree
Yulang.GeneralDictionaryDefaultScopedRevision210.erased {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalCenteredHeadMatStepJournal.State roles}
  {model : Yulang.GeneralNominalCommonBridge.Assignment} {registry : Yulang.GeneralDeclarations.Registry}
  {tree : Yulang.GeneralSourceDictionaries.Dictionary roles} {focus : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {payload : Yulang.CommonRoleOutermostResolver.Dictionary}
  (revision : Yulang.GeneralNominalReobservationSteps.Revision state.core.erased.current)
  (valid :
    Yulang.GeneralNominalCenteredHeadMatStepJournal.Models
      (Yulang.GeneralNominalCenteredHeadMatStepJournal.change state revision.result) model)
  (old :
    Yulang.GeneralSourceDictionaries.Evidence
      (Yulang.GeneralDictionaryTotalEvidence206.Instance registry state.core model) tree)
  (shape : Yulang.GeneralDictionaryDefaultScopedRevision210.Shaped registry state.core.erased.current.context tree)
  (readback : Yulang.GeneralSourceDictionaries.Readback focus payload tree) :
  Yulang.GeneralDictionaryTotalEvidence206.Evidence registry
    (Yulang.GeneralNominalCenteredHeadMatStepJournal.change state revision.result).core model focus payload
Yulang.GeneralDictionaryDefaultScopedRevision210.indexed_iff {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalCenteredHeadMatStepJournal.State roles}
  {model : Yulang.GeneralNominalCommonBridge.Assignment} {registry : Yulang.GeneralDeclarations.Registry}
  {tree : Yulang.GeneralSourceDictionaries.Dictionary roles}
  (revision : Yulang.GeneralNominalReobservationSteps.Revision state.core.erased.current)
  (before : Yulang.GeneralNominalCenteredHeadMatStepJournal.Models state model)
  (after :
    Yulang.GeneralNominalCenteredHeadMatStepJournal.Models
      (Yulang.GeneralNominalCenteredHeadMatStepJournal.change state revision.result) model)
  (shape : Yulang.GeneralDictionaryDefaultScopedRevision210.Shaped registry state.core.erased.current.context tree) :
  Yulang.GeneralSourceDictionaries.Evidence
      (Yulang.GeneralDictionaryTotalEvidence206.Instance registry
        (Yulang.GeneralNominalCenteredHeadMatStepJournal.change state revision.result).core model)
      tree ↔
    Yulang.GeneralSourceDictionaries.Evidence
      (Yulang.GeneralDictionaryTotalEvidence206.Instance registry state.core model) tree
Yulang.GeneralDictionaryDefaultScopedRevision210.certified_indexed_iff {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalCenteredHeadMatStepJournal.State roles}
  {model : Yulang.GeneralNominalCommonBridge.Assignment} {registry : Yulang.GeneralDeclarations.Registry}
  {tree : Yulang.GeneralSourceDictionaries.Dictionary roles}
  (revision : Yulang.GeneralNominalReobservationSteps.Revision state.core.erased.current)
  (certificate : Yulang.GeneralNominalCenteredHeadMatStepRefresh.Reobserve state revision)
  (valid : Yulang.GeneralNominalCenteredHeadMatStepJournal.Models state model)
  (shape : Yulang.GeneralDictionaryDefaultScopedRevision210.Shaped registry state.core.erased.current.context tree) :
  Yulang.GeneralSourceDictionaries.Evidence
      (Yulang.GeneralDictionaryTotalEvidence206.Instance registry
        (Yulang.GeneralNominalCenteredHeadMatStepJournal.change state revision.result).core model)
      tree ↔
    Yulang.GeneralSourceDictionaries.Evidence
      (Yulang.GeneralDictionaryTotalEvidence206.Instance registry state.core model) tree
Yulang.GeneralDictionaryDefaultTerminalOutputs210.generated_actual
  {catalogue : Yulang.GeneralDeclarationPatterns.Constructors}
  {interpretation : Yulang.GeneralNominalInspection.Interpretation}
  (requests : List Yulang.GeneralNominalMaterialization.Request)
  (actual :
    ∀ (request : Yulang.GeneralNominalMaterialization.Request),
      request ∈ requests → request.mode = Yulang.GeneralNominalMaterialization.Mode.actual)
  (equation : Yulang.GeneralNominalCenteredHeadMatSchemas.Equation) :
  equation ∈ (Yulang.GeneralNominalCenteredHeadMatSchemas.generated catalogue interpretation requests).equations →
    equation.mode = Yulang.GeneralNominalMaterialization.Mode.actual
Yulang.GeneralDictionaryDefaultTerminalOutputs210.terminal_requests {roles : Yulang.Roles.RoleDecls}
  (plan : Yulang.GeneralNominalCenters.Plan roles) (terminal : plan.packet.declaration.requirements = []) :
  Yulang.GeneralNominalCenteredHeadMatSchemas.requests plan.packet.context.state plan.packet.registry
      plan.packet.site.occurrence plan.packet.declaration ⋯ plan.packet.bindings =
    Yulang.GeneralNominalMaterialization.rootRequests plan.packet.declaration plan.packet.site.occurrence
Yulang.GeneralDictionaryDefaultTerminalOutputs210.terminal_actual {roles : Yulang.Roles.RoleDecls}
  (plan : Yulang.GeneralNominalCenters.Plan roles) (terminal : plan.packet.declaration.requirements = [])
  (equation : Yulang.GeneralNominalCenteredHeadMatSchemas.Equation) :
  equation ∈ (Yulang.GeneralNominalCenteredHeadMatPlans.emittedSchema plan).equations →
    equation.mode = Yulang.GeneralNominalMaterialization.Mode.actual
Yulang.GeneralDictionaryDefaultTerminalOutputs210.outputs_iff {roles : Yulang.Roles.RoleDecls}
  {first last : Yulang.GeneralNominalCenters.Plan roles} {model : Yulang.GeneralNominalCommonBridge.Assignment}
  (declaration : first.packet.declaration = last.packet.declaration)
  (occurrence : first.packet.site.occurrence = last.packet.site.occurrence)
  (constructors : first.packet.registry.constructors = last.packet.registry.constructors)
  (interpretation : first.packet.context.interpretation = last.packet.context.interpretation)
  (terminal : first.packet.declaration.requirements = [])
  (names : ∀ (name : Nat), first.binder name = last.binder name) :
  Yulang.GeneralNominalCenteredHeadMatStepPackets.Outputs first model ↔
    Yulang.GeneralNominalCenteredHeadMatStepPackets.Outputs last model
Yulang.GeneralDictionaryDefaultNominalFrame210.frame {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalCenteredHeadMatStepJournal.State roles}
  {revision : Yulang.GeneralNominalReobservationSteps.Revision state.core.erased.current}
  {focus : Yulang.GeneralSourceDictionaries.Occurrence roles} {key : Nat}
  (s : Yulang.GeneralDictionarySemanticCollapse.Shape revision) (registry : Yulang.GeneralDeclarations.Registry)
  (site : Yulang.GeneralNominalDemandMerging.Site roles) (declaration : Yulang.GeneralDeclarations.Declaration)
  (checked : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration)
  (center : Yulang.GeneralNominalCenters.Site roles) (same : center.occurrence = site.occurrence)
  (queries :
    Yulang.GeneralNominalInspection.queries state.core.erased.current.context.state
        state.core.erased.current.context.interpretation declaration =
      [Yulang.GeneralDictionarySemanticCollapse.query s])
  (old :
    Yulang.GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key
      (Yulang.GeneralDictionaryDefaultNonpointTerminal210.oldPlan s registry site declaration checked center same))
  (model : Yulang.GeneralNominalCommonBridge.Assignment)
  (held :
    Yulang.GeneralNominalCenteredHeadMatStepPackets.Holds
      (Yulang.GeneralDictionaryDefaultNonpointTerminal210.newPlan s registry site declaration checked center same)
      model) :
  Yulang.GeneralNominalCenteredHeadOutputs.Frame registry
    (Yulang.GeneralNominalCenteredHeadMatStepJournal.change state revision.result).core focus key
    (Yulang.GeneralDictionaryDefaultNonpointTerminal210.newPlan s registry site declaration checked center same)
Yulang.GeneralDictionaryDefaultNominalFrame210.certificate {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalCenteredHeadMatStepJournal.State roles}
  {revision : Yulang.GeneralNominalReobservationSteps.Revision state.core.erased.current}
  {focus : Yulang.GeneralSourceDictionaries.Occurrence roles} {key : Nat}
  {children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)}
  (s : Yulang.GeneralDictionarySemanticCollapse.Shape revision) (registry : Yulang.GeneralDeclarations.Registry)
  (site : Yulang.GeneralNominalDemandMerging.Site roles) (declaration : Yulang.GeneralDeclarations.Declaration)
  (checked : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration)
  (center : Yulang.GeneralNominalCenters.Site roles) (same : center.occurrence = site.occurrence)
  (queries :
    Yulang.GeneralNominalInspection.queries state.core.erased.current.context.state
        state.core.erased.current.context.interpretation declaration =
      [Yulang.GeneralDictionarySemanticCollapse.query s])
  (names : declaration.inputNames = [s.binder]) (terminal : declaration.requirements = [])
  (nonpoint :
    (Yulang.GeneralDictionarySemanticCollapseAllocation.firstPair s).fst ≠
      (Yulang.GeneralDictionarySemanticCollapseAllocation.firstPair s).snd)
  (model : Yulang.GeneralNominalCommonBridge.Assignment)
  (old :
    Yulang.GeneralDictionaryTotalEvidence206.Certificate registry state.core model focus key children
      (Yulang.GeneralDictionaryDefaultNonpointTerminal210.oldPlan s registry site declaration checked center same))
  (current : Yulang.GeneralNominalState.Models revision.snapshot model) :
  Yulang.GeneralDictionaryTotalEvidence206.Certificate registry
    (Yulang.GeneralNominalCenteredHeadMatStepJournal.change state revision.result).core model focus key children
    (Yulang.GeneralDictionaryDefaultNonpointTerminal210.newPlan s registry site declaration checked center same)
```
