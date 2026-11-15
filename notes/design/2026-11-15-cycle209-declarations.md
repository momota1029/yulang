# Cycle209 exact checked theorem types

102 declarations from17 new modules. All are auxiliary, restricted-fragment soundness, or regression results; unrestricted EvidenceNode/FreshCompletion remain open. Full quantified Lean types below were emitted with lean --trust=0 -DwarningAsError=true, exit0. Classifications and limits: [cycle report](../handoff/dots-cycle-209.md).

```lean
Yulang.GeneralDictionaryDefaultBodyTransport209.actual_only
  {environment : Yulang.GeneralNominalMaterialization.Mode → Nat → Yulang.CommonNominalFullCarrier.Ty}
  (expression : Yulang.GeneralNominalCenteredHeadMatExpressions.Expr) :
  Yulang.GeneralNominalCenteredHeadMatExpressions.value
      (fun x name => environment Yulang.GeneralNominalMaterialization.Mode.actual name)
      Yulang.GeneralNominalMaterialization.Mode.actual expression =
    Yulang.GeneralNominalCenteredHeadMatExpressions.value environment Yulang.GeneralNominalMaterialization.Mode.actual
      expression
Yulang.GeneralDictionaryDefaultBodyTransport209.actuals_only
  {environment : Yulang.GeneralNominalMaterialization.Mode → Nat → Yulang.CommonNominalFullCarrier.Ty}
  (expressions : List Yulang.GeneralNominalCenteredHeadMatExpressions.Expr) :
  Yulang.GeneralNominalCenteredHeadMatExpressions.values
      (fun x name => environment Yulang.GeneralNominalMaterialization.Mode.actual name)
      Yulang.GeneralNominalMaterialization.Mode.actual expressions =
    Yulang.GeneralNominalCenteredHeadMatExpressions.values environment Yulang.GeneralNominalMaterialization.Mode.actual
      expressions
Yulang.GeneralDictionaryDefaultBodyTransport209.actual_equivalent
  {one two : Yulang.GeneralNominalMaterialization.Mode → Nat → Yulang.CommonNominalFullCarrier.Ty}
  (expression : Yulang.GeneralNominalCenteredHeadMatExpressions.Expr)
  (same :
    ∀ (name : Nat),
      name ∈ Yulang.GeneralNominalCenteredHeadMatExtension.names expression →
        Yulang.CommonNominalFullCarrier.Equivalent (one Yulang.GeneralNominalMaterialization.Mode.actual name)
          (two Yulang.GeneralNominalMaterialization.Mode.actual name)) :
  Yulang.CommonNominalFullCarrier.Equivalent
    (Yulang.GeneralNominalCenteredHeadMatExpressions.value one Yulang.GeneralNominalMaterialization.Mode.actual
      expression)
    (Yulang.GeneralNominalCenteredHeadMatExpressions.value two Yulang.GeneralNominalMaterialization.Mode.actual
      expression)
Yulang.GeneralDictionaryDefaultBodyTransport209.compile_equal {roles : Yulang.Roles.RoleDecls}
  {first last : Yulang.GeneralNominalCenters.Plan roles}
  (constructors : first.packet.registry.constructors = last.packet.registry.constructors)
  (interpretation : first.packet.context.interpretation = last.packet.context.interpretation)
  (body : Yulang.GeneralDictionaryAssociatedProvenance.Body) :
  Yulang.GeneralNominalCenteredHeadMatEffects.compileBody first body =
    Yulang.GeneralNominalCenteredHeadMatEffects.compileBody last body
Yulang.GeneralDictionaryDefaultBodyTransport209.body_holds_iff {roles : Yulang.Roles.RoleDecls}
  {first last : Yulang.GeneralNominalCenters.Plan roles} {model : Yulang.GeneralNominalCommonBridge.Assignment}
  {body : Yulang.GeneralDictionaryAssociatedProvenance.Body}
  {expression : Yulang.GeneralNominalCenteredHeadMatExpressions.Expr} {target : Nat}
  (translated : Yulang.GeneralNominalCenteredHeadMatEffects.compileBody first body = some expression)
  (translated' : Yulang.GeneralNominalCenteredHeadMatEffects.compileBody last body = some expression)
  (same :
    ∀ (name : Nat),
      name ∈ Yulang.GeneralNominalCenteredHeadMatExtension.names expression →
        Yulang.CommonNominalFullCarrier.Equivalent
          (Yulang.GeneralNominalCenteredHeadMatEffects.bodyVariables first model body
            Yulang.GeneralNominalMaterialization.Mode.actual name)
          (Yulang.GeneralNominalCenteredHeadMatEffects.bodyVariables last model body
            Yulang.GeneralNominalMaterialization.Mode.actual name)) :
  Yulang.GeneralNominalCenteredHeadMatEffects.BodyHolds first target model body ↔
    Yulang.GeneralNominalCenteredHeadMatEffects.BodyHolds last target model body
Yulang.GeneralDictionaryDefaultBodyTransport209.actual_variables {roles : Yulang.Roles.RoleDecls}
  (plan : Yulang.GeneralNominalCenters.Plan roles) (model : Yulang.GeneralNominalCommonBridge.Assignment) (name : Nat) :
  Yulang.GeneralNominalCenteredHeadMatEffects.variables plan model Yulang.GeneralNominalMaterialization.Mode.actual
      name =
    (model (plan.binder name)).fst
Yulang.GeneralDictionaryDefaultBodyTransport209.semantic_body_variables {roles : Yulang.Roles.RoleDecls}
  {first last : Yulang.GeneralNominalCenters.Plan roles} {model : Yulang.GeneralNominalCommonBridge.Assignment}
  (binders :
    ∀ (name : Nat),
      Yulang.CommonNominalFullCarrier.Equivalent (model (first.binder name)).fst (model (last.binder name)).fst)
  (centers :
    ∀ (index : Nat),
      Yulang.CommonNominalFullCarrier.Equivalent (model ((List.ofFn first.input.center)[index]?.getD 0)).fst
        (model ((List.ofFn last.input.center)[index]?.getD 0)).fst)
  (body : Yulang.GeneralDictionaryAssociatedProvenance.Body) (name : Nat) :
  Yulang.CommonNominalFullCarrier.Equivalent
    (Yulang.GeneralNominalCenteredHeadMatEffects.bodyVariables first model body
      Yulang.GeneralNominalMaterialization.Mode.actual name)
    (Yulang.GeneralNominalCenteredHeadMatEffects.bodyVariables last model body
      Yulang.GeneralNominalMaterialization.Mode.actual name)
Yulang.GeneralDictionaryDefaultBodyTransport209.body_transport {roles : Yulang.Roles.RoleDecls}
  {first last : Yulang.GeneralNominalCenters.Plan roles} {model : Yulang.GeneralNominalCommonBridge.Assignment}
  {target : Nat} {body : Yulang.GeneralDictionaryAssociatedProvenance.Body}
  (constructors : first.packet.registry.constructors = last.packet.registry.constructors)
  (interpretation : first.packet.context.interpretation = last.packet.context.interpretation)
  (binders :
    ∀ (name : Nat),
      Yulang.CommonNominalFullCarrier.Equivalent (model (first.binder name)).fst (model (last.binder name)).fst)
  (centers :
    ∀ (index : Nat),
      Yulang.CommonNominalFullCarrier.Equivalent (model ((List.ofFn first.input.center)[index]?.getD 0)).fst
        (model ((List.ofFn last.input.center)[index]?.getD 0)).fst) :
  Yulang.GeneralNominalCenteredHeadMatEffects.BodyHolds first target model body ↔
    Yulang.GeneralNominalCenteredHeadMatEffects.BodyHolds last target model body
Yulang.GeneralDictionaryDefaultCollapsedCenters209.centers_equivalent {roles : Yulang.Roles.RoleDecls}
  {model : Yulang.GeneralNominalCommonBridge.Assignment} (first last : Yulang.GeneralNominalCenters.Site roles)
  (same : first.occurrence = last.occurrence)
  (collapsed :
    ∀ (index : Fin (roles first.occurrence.demand.role).arity),
      Yulang.CommonNominalFullCarrier.Equivalent (model (first.occurrence.demand.arguments index).fst).fst
        (model (first.occurrence.demand.arguments index).snd).fst)
  (one : first.Holds model) (two : last.Holds model) (index : Nat) :
  Yulang.CommonNominalFullCarrier.Equivalent (model ((List.ofFn first.center)[index]?.getD 0)).fst
    (model ((List.ofFn last.center)[index]?.getD 0)).fst
Yulang.GeneralDictionaryDefaultCollapsedCenters209.recenter_holds {roles : Yulang.Roles.RoleDecls}
  {model : Yulang.GeneralNominalCommonBridge.Assignment} {historical : Yulang.GeneralNominalCenters.Plan roles}
  (site : Yulang.GeneralNominalCenters.Site roles) (same : site.occurrence = historical.packet.site.occurrence)
  (collapsed :
    ∀ (index : Fin (roles historical.input.occurrence.demand.role).arity),
      Yulang.CommonNominalFullCarrier.Equivalent (model (historical.input.occurrence.demand.arguments index).fst).fst
        (model (historical.input.occurrence.demand.arguments index).snd).fst)
  (center : site.Holds model) (old : Yulang.GeneralNominalCenteredHeadMatStepPackets.Holds historical model) :
  Yulang.GeneralNominalCenteredHeadMatStepPackets.Holds
    (Yulang.GeneralDictionaryDefaultSemanticReplay209.recenter historical site same) model
Yulang.GeneralDictionaryDefaultCollapsedCenters209.recenter_class {roles : Yulang.Roles.RoleDecls}
  {model : Yulang.GeneralNominalCommonBridge.Assignment} {core : Yulang.GeneralNominalCenteredSteps.State roles}
  {focus : Yulang.GeneralSourceDictionaries.Occurrence roles} {historical : Yulang.GeneralNominalCenters.Plan roles}
  (site : Yulang.GeneralNominalCenters.Site roles) (same : site.occurrence = historical.packet.site.occurrence)
  (collapsed :
    ∀ (index : Fin (roles historical.input.occurrence.demand.role).arity),
      Yulang.CommonNominalFullCarrier.Equivalent (model (historical.input.occurrence.demand.arguments index).fst).fst
        (model (historical.input.occurrence.demand.arguments index).snd).fst)
  (center : site.Holds model) (input : historical.input.Holds model) :
  Yulang.GeneralNominalCenteredHeadMatEffects.ClassEffects core focus historical model ↔
    Yulang.GeneralNominalCenteredHeadMatEffects.ClassEffects core focus
      (Yulang.GeneralDictionaryDefaultSemanticReplay209.recenter historical site same) model
Yulang.GeneralDictionaryDefaultCollapsedCenters209.certificate {roles : Yulang.Roles.RoleDecls}
  {model : Yulang.GeneralNominalCommonBridge.Assignment}
  {value : (Yulang.GeneralNominalCenteredHeadMatStepLocal.vocabulary roles).Registry}
  {root : (Yulang.GeneralNominalCenteredHeadMatStepLocal.vocabulary roles).Demand}
  {focus : Yulang.GeneralSourceDictionaries.Occurrence roles} {key : Nat}
  {state : Yulang.GeneralNominalCenteredHeadMatStepJournal.State roles}
  {current historical : Yulang.GeneralNominalCenters.Plan roles}
  (checked : (Yulang.GeneralDictionaryDefaultBoundary208.boundary roles).Checked value)
  (reachable : Yulang.B4TargetV7.Reachable (Yulang.GeneralDictionaryDefaultBoundary208.boundary roles) value root state)
  (frame :
    Yulang.GeneralNominalCenteredHeadOutputs.Frame (Yulang.GeneralNominalCenteredHeadAllocEncoding.registry value)
      state.core focus key current)
  (member : historical ∈ state.core.plans) (keyEq : historical.packet.declaration.id = key)
  (occurrence : historical.packet.site.occurrence = focus)
  (collapsed :
    ∀ (index : Fin (roles focus.demand.role).arity),
      Yulang.CommonNominalFullCarrier.Equivalent (model (focus.demand.arguments index).fst).fst
        (model (focus.demand.arguments index).snd).fst)
  (report :
    Yulang.GeneralNominalReportErasure.erase current.packet.context.state
        (Yulang.GeneralNominalPacketSupport.report current.packet) =
      Yulang.GeneralNominalReportErasure.erase historical.packet.context.state
        (Yulang.GeneralNominalPacketSupport.report historical.packet))
  (valid : Yulang.GeneralNominalCenteredHeadMatStepJournal.Models state model) :
  Yulang.GeneralDictionaryTotalEvidence206.Certificate (Yulang.GeneralNominalCenteredHeadAllocEncoding.registry value)
    state.core model focus key current.packet.children current
Yulang.GeneralDictionaryDefaultCollapsedCenters209.nominal_certificate {roles : Yulang.Roles.RoleDecls}
  {model : Yulang.GeneralNominalCommonBridge.Assignment}
  {value : (Yulang.GeneralNominalCenteredHeadMatStepLocal.vocabulary roles).Registry}
  {root : (Yulang.GeneralNominalCenteredHeadMatStepLocal.vocabulary roles).Demand}
  {focus : Yulang.GeneralSourceDictionaries.Occurrence roles} {key : Nat}
  {state : Yulang.GeneralNominalCenteredHeadMatStepJournal.State roles}
  {current historical : Yulang.GeneralNominalCenters.Plan roles}
  (checked : (Yulang.GeneralDictionaryDefaultBoundary208.boundary roles).Checked value)
  (reachable : Yulang.B4TargetV7.Reachable (Yulang.GeneralDictionaryDefaultBoundary208.boundary roles) value root state)
  (frame :
    Yulang.GeneralNominalCenteredHeadOutputs.Frame (Yulang.GeneralNominalCenteredHeadAllocEncoding.registry value)
      state.core focus key current)
  (member : historical ∈ state.core.plans) (keyEq : historical.packet.declaration.id = key)
  (occurrence : historical.packet.site.occurrence = focus)
  (collapsed :
    ∀ (index : Fin (roles focus.demand.role).arity),
      Yulang.CommonNominalFullCarrier.Equivalent (model (focus.demand.arguments index).fst).fst
        (model (focus.demand.arguments index).snd).fst)
  (refinement : Yulang.GeneralNominalRefinements.Refines historical.packet.context.state current.packet.context.state)
  (shape :
    ∀ (query : Yulang.GeneralNominalInspection.Query),
      query ∈
          Yulang.GeneralNominalInspection.queries historical.packet.context.state
            historical.packet.context.interpretation historical.packet.declaration →
        Yulang.GeneralNominalFinishedObservation197.Syntax query)
  (valid : Yulang.GeneralNominalCenteredHeadMatStepJournal.Models state model) :
  Yulang.GeneralDictionaryTotalEvidence206.Certificate (Yulang.GeneralNominalCenteredHeadAllocEncoding.registry value)
    state.core model focus key current.packet.children current
Yulang.GeneralDictionaryDefaultCollapsedExamples209.interval_holds (name : Nat) :
  (Yulang.GeneralDictionaryDefaultTransportExamples209.intervalSite name).Holds
    Yulang.GeneralDictionaryDefaultGap206Source.model
Yulang.GeneralDictionaryDefaultCollapsedExamples209.interval_collapsed
  (index :
    Fin
      (Yulang.GeneralDictionaryDefaultGap206Source.roles
          Yulang.GeneralDictionaryDefaultTransportExamples209.intervalRoot.demand.role).arity) :
  Yulang.CommonNominalFullCarrier.Equivalent
    (Yulang.GeneralDictionaryDefaultGap206Source.model
        (Yulang.GeneralDictionaryDefaultTransportExamples209.intervalRoot.demand.arguments index).fst).fst
    (Yulang.GeneralDictionaryDefaultGap206Source.model
        (Yulang.GeneralDictionaryDefaultTransportExamples209.intervalRoot.demand.arguments index).snd).fst
Yulang.GeneralDictionaryDefaultCollapsedExamples209.nonpoint_centers (index : Nat) :
  Yulang.CommonNominalFullCarrier.Equivalent
    (Yulang.GeneralDictionaryDefaultGap206Source.model
        ((List.ofFn (Yulang.GeneralDictionaryDefaultTransportExamples209.intervalSite 0).center)[index]?.getD 0)).fst
    (Yulang.GeneralDictionaryDefaultGap206Source.model
        ((List.ofFn (Yulang.GeneralDictionaryDefaultTransportExamples209.intervalSite 1).center)[index]?.getD 0)).fst
Yulang.GeneralDictionaryDefaultCollapsedExamples209.nonpoint_default_transport :
  Yulang.GeneralNominalCenteredHeadMatEffects.BodyHolds
      (Yulang.GeneralDictionaryDefaultTransportExamples209.intervalPlan 0) 0
      Yulang.GeneralDictionaryDefaultGap206Source.model
      (Yulang.GeneralDictionaryAssociatedProvenance.Body.default 0 0 (Yulang.Roles.Term.var 0)) ↔
    Yulang.GeneralNominalCenteredHeadMatEffects.BodyHolds
      (Yulang.GeneralDictionaryDefaultTransportExamples209.intervalPlan 1) 0
      Yulang.GeneralDictionaryDefaultGap206Source.model
      (Yulang.GeneralDictionaryAssociatedProvenance.Body.default 0 0 (Yulang.Roles.Term.var 0))
Yulang.GeneralDictionaryDefaultConfiguration209.seed {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalCenteredHeadMatStepJournal.State roles} {value : Yulang.GeneralDeclarations.Registry}
  {context : Yulang.GeneralNominalCandidates.Context} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  (built : Yulang.GeneralNominalCenteredHeadMatStepHistory.Built value context root state) :
  state.core.erased.current.context.state.seed = context.state.seed
Yulang.GeneralDictionaryDefaultConfiguration209.frame_constructors {value : Yulang.GeneralDeclarations.Registry}
  {roles✝ : Yulang.Roles.RoleDecls} {core : Yulang.GeneralNominalCenteredSteps.State roles✝}
  {focus : Yulang.GeneralSourceDictionaries.Occurrence roles✝} {key : Nat}
  {plan : Yulang.GeneralNominalCenters.Plan roles✝}
  (frame : Yulang.GeneralNominalCenteredHeadOutputs.Frame value core focus key plan) :
  plan.packet.context.state.constructors = value.constructors
Yulang.GeneralDictionaryDefaultConfiguration209.stored {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalCenteredHeadMatStepJournal.State roles} {value : Yulang.GeneralDeclarations.Registry}
  {context : Yulang.GeneralNominalCandidates.Context} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {plan : Yulang.GeneralNominalCenters.Plan roles}
  (built : Yulang.GeneralNominalCenteredHeadMatStepHistory.Built value context root state)
  (member : plan ∈ state.core.plans) :
  plan.packet.registry = value ∧
    plan.packet.context.state.seed = context.state.seed ∧
      plan.packet.context.interpretation = context.interpretation ∧
        plan.packet.context.state.constructors = value.constructors
Yulang.GeneralDictionaryDefaultConfiguration209.reinspection_data {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalCenteredHeadMatStepJournal.State roles}
  {value : (Yulang.GeneralNominalCenteredHeadMatStepLocal.vocabulary roles).Registry}
  {root : (Yulang.GeneralNominalCenteredHeadMatStepLocal.vocabulary roles).Demand}
  {focus : Yulang.GeneralSourceDictionaries.Occurrence roles} {key : Nat}
  {current historical : Yulang.GeneralNominalCenters.Plan roles}
  (reachable : Yulang.B4TargetV7.Reachable (Yulang.GeneralDictionaryDefaultBoundary208.boundary roles) value root state)
  (frame :
    Yulang.GeneralNominalCenteredHeadOutputs.Frame (Yulang.GeneralNominalCenteredHeadAllocEncoding.registry value)
      state.core focus key current)
  (member : historical ∈ state.core.plans) (declaration : current.packet.declaration = historical.packet.declaration)
  (input : current.input = historical.input)
  (report :
    Yulang.GeneralNominalReportErasure.erase current.packet.context.state
        (Yulang.GeneralNominalPacketSupport.report current.packet) =
      Yulang.GeneralNominalReportErasure.erase historical.packet.context.state
        (Yulang.GeneralNominalPacketSupport.report historical.packet)) :
  Yulang.GeneralNominalCenteredHeadMatPlanData.Same current historical
Yulang.GeneralDictionaryDefaultCurrentCertificate209.frame_data {roles : Yulang.Roles.RoleDecls}
  {first last : Yulang.GeneralNominalCenters.Plan roles} {state : Yulang.GeneralNominalCenteredSteps.State roles}
  {focus : Yulang.GeneralSourceDictionaries.Occurrence roles} {key : Nat} {reg : Yulang.GeneralDeclarations.Registry}
  (checked : Yulang.GeneralDeclarations.Checked reg)
  (one : Yulang.GeneralNominalCenteredHeadOutputs.Frame reg state focus key first)
  (two : Yulang.GeneralNominalCenteredHeadOutputs.Frame reg state focus key last)
  (same : first.input.occurrence = last.packet.site.occurrence) :
  Yulang.GeneralNominalCenteredHeadMatPlanData.Same first
    (Yulang.GeneralDictionaryDefaultSemanticReplay209.recenter last first.input same)
Yulang.GeneralDictionaryDefaultCurrentCertificate209.transport {roles : Yulang.Roles.RoleDecls}
  {first last : Yulang.GeneralNominalCenters.Plan roles}
  {value : (Yulang.GeneralNominalCenteredHeadMatStepLocal.vocabulary roles).Registry}
  {focus : Yulang.GeneralSourceDictionaries.Occurrence roles} {key : Nat}
  {model : Yulang.GeneralNominalCommonBridge.Assignment}
  {children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)}
  {state : Yulang.GeneralNominalCenteredHeadMatStepJournal.State roles}
  (checked : (Yulang.GeneralDictionaryDefaultBoundary208.boundary roles).Checked value)
  (frame :
    Yulang.GeneralNominalCenteredHeadOutputs.Frame (Yulang.GeneralNominalCenteredHeadAllocEncoding.registry value)
      state.core focus key first)
  (point :
    ∀ (index : Fin (roles focus.demand.role).arity),
      (focus.demand.arguments index).fst = (focus.demand.arguments index).snd)
  (valid : Yulang.GeneralNominalCenteredHeadMatStepJournal.Models state model)
  (old :
    Yulang.GeneralDictionaryTotalEvidence206.Certificate (Yulang.GeneralNominalCenteredHeadAllocEncoding.registry value)
      state.core model focus key children last) :
  Yulang.GeneralDictionaryTotalEvidence206.Certificate (Yulang.GeneralNominalCenteredHeadAllocEncoding.registry value)
    state.core model focus key children first
Yulang.GeneralDictionaryDefaultCurrentCertificate209.instance_iff {roles : Yulang.Roles.RoleDecls}
  {first : Yulang.GeneralNominalCenters.Plan roles}
  {value : (Yulang.GeneralNominalCenteredHeadMatStepLocal.vocabulary roles).Registry}
  {focus : Yulang.GeneralSourceDictionaries.Occurrence roles} {key : Nat}
  {model : Yulang.GeneralNominalCommonBridge.Assignment}
  {children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)}
  {state : Yulang.GeneralNominalCenteredHeadMatStepJournal.State roles}
  (checked : (Yulang.GeneralDictionaryDefaultBoundary208.boundary roles).Checked value)
  (frame :
    Yulang.GeneralNominalCenteredHeadOutputs.Frame (Yulang.GeneralNominalCenteredHeadAllocEncoding.registry value)
      state.core focus key first)
  (point :
    ∀ (index : Fin (roles focus.demand.role).arity),
      (focus.demand.arguments index).fst = (focus.demand.arguments index).snd)
  (valid : Yulang.GeneralNominalCenteredHeadMatStepJournal.Models state model) :
  Yulang.GeneralDictionaryTotalEvidence206.Instance (Yulang.GeneralNominalCenteredHeadAllocEncoding.registry value)
      state.core model focus key children ↔
    Yulang.GeneralDictionaryTotalEvidence206.Certificate (Yulang.GeneralNominalCenteredHeadAllocEncoding.registry value)
      state.core model focus key children first
Yulang.GeneralDictionaryDefaultCurrentCertificate209.node_iff {roles : Yulang.Roles.RoleDecls}
  {first : Yulang.GeneralNominalCenters.Plan roles}
  {value : (Yulang.GeneralNominalCenteredHeadMatStepLocal.vocabulary roles).Registry}
  {focus : Yulang.GeneralSourceDictionaries.Occurrence roles} {key : Nat}
  {model : Yulang.GeneralNominalCommonBridge.Assignment}
  {dictionaries : List Yulang.CommonRoleOutermostResolver.Dictionary}
  {state : Yulang.GeneralNominalCenteredHeadMatStepJournal.State roles}
  (checked : (Yulang.GeneralDictionaryDefaultBoundary208.boundary roles).Checked value)
  (frame :
    Yulang.GeneralNominalCenteredHeadOutputs.Frame (Yulang.GeneralNominalCenteredHeadAllocEncoding.registry value)
      state.core focus key first)
  (point :
    ∀ (index : Fin (roles focus.demand.role).arity),
      (focus.demand.arguments index).fst = (focus.demand.arguments index).snd)
  (valid : Yulang.GeneralNominalCenteredHeadMatStepJournal.Models state model) :
  Yulang.GeneralDictionaryTotalEvidence206.Evidence (Yulang.GeneralNominalCenteredHeadAllocEncoding.registry value)
      state.core model focus (Yulang.CommonRoleOutermostResolver.Dictionary.node key dictionaries) ↔
    Yulang.GeneralDictionaryTotalEvidence206.Certificate (Yulang.GeneralNominalCenteredHeadAllocEncoding.registry value)
        state.core model focus key first.packet.children first ∧
      Yulang.CommonRoleOutermostResolver.All₂
        (Yulang.GeneralDictionaryTotalEvidence206.Evidence
          (Yulang.GeneralNominalCenteredHeadAllocEncoding.registry value) state.core model)
        first.packet.children dictionaries
Yulang.GeneralDictionaryDefaultExpression209.equivalent_refl (type : Yulang.CommonNominalFullCarrier.Ty) :
  Yulang.CommonNominalFullCarrier.Equivalent type type
Yulang.GeneralDictionaryDefaultExpression209.equivalent_trans {first middle last : Yulang.CommonNominalFullCarrier.Ty}
  (one : Yulang.CommonNominalFullCarrier.Equivalent first middle)
  (two : Yulang.CommonNominalFullCarrier.Equivalent middle last) : Yulang.CommonNominalFullCarrier.Equivalent first last
Yulang.GeneralDictionaryDefaultExpression209.primitive_equivalent {first last : List Yulang.CommonNominalFullCarrier.Ty}
  (constructor : Yulang.GeneralCandidateInspection.Primitive)
  (same : Yulang.CommonRoleOutermostResolver.All₂ Yulang.CommonNominalFullCarrier.Equivalent first last) :
  Yulang.CommonNominalFullCarrier.Equivalent
    (Yulang.GeneralNominalCenteredHeadMatExpressions.primitiveValue constructor first)
    (Yulang.GeneralNominalCenteredHeadMatExpressions.primitiveValue constructor last)
Yulang.GeneralDictionaryDefaultExpression209.list_length {first last : List Yulang.CommonNominalFullCarrier.Ty}
  (same : Yulang.CommonRoleOutermostResolver.All₂ Yulang.CommonNominalFullCarrier.Equivalent first last) :
  first.length = last.length
Yulang.GeneralDictionaryDefaultExpression209.list_get {first last : List Yulang.CommonNominalFullCarrier.Ty}
  {a b : Yulang.CommonNominalFullCarrier.Ty} {index : Nat}
  (same : Yulang.CommonRoleOutermostResolver.All₂ Yulang.CommonNominalFullCarrier.Equivalent first last)
  (left : first[index]? = some a) (right : last[index]? = some b) : Yulang.CommonNominalFullCarrier.Equivalent a b
Yulang.GeneralDictionaryDefaultExpression209.list_symm {first last : List Yulang.CommonNominalFullCarrier.Ty}
  (same : Yulang.CommonRoleOutermostResolver.All₂ Yulang.CommonNominalFullCarrier.Equivalent first last) :
  Yulang.CommonRoleOutermostResolver.All₂ Yulang.CommonNominalFullCarrier.Equivalent last first
Yulang.GeneralDictionaryDefaultExpression209.nominal_equivalent {first last : List Yulang.CommonNominalFullCarrier.Ty}
  (name : Nat) (same : Yulang.CommonRoleOutermostResolver.All₂ Yulang.CommonNominalFullCarrier.Equivalent first last) :
  Yulang.CommonNominalFullCarrier.Equivalent (Yulang.CommonNominalFullCarrier.nominal name (List.map Sum.inl first))
    (Yulang.CommonNominalFullCarrier.nominal name (List.map Sum.inl last))
Yulang.GeneralDictionaryDefaultExpression209.value_equivalent
  {first last : Yulang.GeneralNominalMaterialization.Mode → Nat → Yulang.CommonNominalFullCarrier.Ty}
  {mode : Yulang.GeneralNominalMaterialization.Mode} (expression : Yulang.GeneralNominalCenteredHeadMatExpressions.Expr)
  (agree :
    ∀ (mode : Yulang.GeneralNominalMaterialization.Mode) (name : Nat),
      name ∈ Yulang.GeneralNominalCenteredHeadMatExtension.names expression →
        Yulang.CommonNominalFullCarrier.Equivalent (first mode name) (last mode name)) :
  Yulang.CommonNominalFullCarrier.Equivalent
    (Yulang.GeneralNominalCenteredHeadMatExpressions.value first mode expression)
    (Yulang.GeneralNominalCenteredHeadMatExpressions.value last mode expression)
Yulang.GeneralDictionaryDefaultExpression209.values_equivalent
  {first last : Yulang.GeneralNominalMaterialization.Mode → Nat → Yulang.CommonNominalFullCarrier.Ty}
  {mode : Yulang.GeneralNominalMaterialization.Mode}
  (expressions : List Yulang.GeneralNominalCenteredHeadMatExpressions.Expr)
  (agree :
    ∀ (mode : Yulang.GeneralNominalMaterialization.Mode) (name : Nat),
      name ∈ Yulang.GeneralNominalCenteredHeadMatExtension.namesMany expressions →
        Yulang.CommonNominalFullCarrier.Equivalent (first mode name) (last mode name)) :
  Yulang.CommonRoleOutermostResolver.All₂ Yulang.CommonNominalFullCarrier.Equivalent
    (Yulang.GeneralNominalCenteredHeadMatExpressions.values first mode expressions)
    (Yulang.GeneralNominalCenteredHeadMatExpressions.values last mode expressions)
Yulang.GeneralDictionaryDefaultFrame209.frame_children {registry : Yulang.GeneralDeclarations.Registry}
  {roles✝ : Yulang.Roles.RoleDecls} {state : Yulang.GeneralNominalCenteredSteps.State roles✝}
  {focus : Yulang.GeneralSourceDictionaries.Occurrence roles✝} {key : Nat}
  {first last : Yulang.GeneralNominalCenters.Plan roles✝} (checked : Yulang.GeneralDeclarations.Checked registry)
  (one : Yulang.GeneralNominalCenteredHeadOutputs.Frame registry state focus key first)
  (two : Yulang.GeneralNominalCenteredHeadOutputs.Frame registry state focus key last) :
  first.packet.children = last.packet.children
Yulang.GeneralDictionaryDefaultFrame209.certificate_children {registry : Yulang.GeneralDeclarations.Registry}
  {roles✝ : Yulang.Roles.RoleDecls} {state : Yulang.GeneralNominalCenteredSteps.State roles✝}
  {model : Yulang.GeneralNominalCommonBridge.Assignment} {focus : Yulang.GeneralSourceDictionaries.Occurrence roles✝}
  {key : Nat} {children : List (Yulang.GeneralSourceDictionaries.Occurrence roles✝)}
  {first : Yulang.GeneralNominalCenters.Plan roles✝} {otherModel : Yulang.GeneralNominalCommonBridge.Assignment}
  {otherChildren : List (Yulang.GeneralSourceDictionaries.Occurrence roles✝)}
  {last : Yulang.GeneralNominalCenters.Plan roles✝} (checked : Yulang.GeneralDeclarations.Checked registry)
  (one : Yulang.GeneralDictionaryTotalEvidence206.Certificate registry state model focus key children first)
  (two : Yulang.GeneralDictionaryTotalEvidence206.Certificate registry state otherModel focus key otherChildren last) :
  children = otherChildren
Yulang.GeneralDictionaryDefaultFrame209.instance_children {registry : Yulang.GeneralDeclarations.Registry}
  {roles✝ : Yulang.Roles.RoleDecls} {state : Yulang.GeneralNominalCenteredSteps.State roles✝}
  {model : Yulang.GeneralNominalCommonBridge.Assignment} {focus : Yulang.GeneralSourceDictionaries.Occurrence roles✝}
  {key : Nat} {children : List (Yulang.GeneralSourceDictionaries.Occurrence roles✝)}
  {otherModel : Yulang.GeneralNominalCommonBridge.Assignment}
  {otherChildren : List (Yulang.GeneralSourceDictionaries.Occurrence roles✝)}
  (checked : Yulang.GeneralDeclarations.Checked registry)
  (one : Yulang.GeneralDictionaryTotalEvidence206.Instance registry state model focus key children)
  (two : Yulang.GeneralDictionaryTotalEvidence206.Instance registry state otherModel focus key otherChildren) :
  children = otherChildren
Yulang.GeneralDictionaryDefaultFrame209.childrenFunctional {registry : Yulang.GeneralDeclarations.Registry}
  {roles✝ : Yulang.Roles.RoleDecls} {state : Yulang.GeneralNominalCenteredSteps.State roles✝}
  {model : Yulang.GeneralNominalCommonBridge.Assignment} (checked : Yulang.GeneralDeclarations.Checked registry) :
  Yulang.GeneralDictionaryReadback.ChildrenFunctional
    (Yulang.GeneralDictionaryTotalEvidence206.Instance registry state model)
Yulang.GeneralDictionaryDefaultFrameSemantics209.declaration {roles : Yulang.Roles.RoleDecls}
  {first last : Yulang.GeneralNominalCenters.Plan roles} {registry : Yulang.GeneralDeclarations.Registry}
  {state : Yulang.GeneralNominalCenteredSteps.State roles} {focus : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {key : Nat} (checked : Yulang.GeneralDeclarations.Checked registry)
  (one : Yulang.GeneralNominalCenteredHeadOutputs.Frame registry state focus key first)
  (two : Yulang.GeneralNominalCenteredHeadOutputs.Frame registry state focus key last) :
  first.packet.declaration = last.packet.declaration
Yulang.GeneralDictionaryDefaultFrameSemantics209.binder {roles : Yulang.Roles.RoleDecls}
  {first last : Yulang.GeneralNominalCenters.Plan roles} {registry : Yulang.GeneralDeclarations.Registry}
  {state : Yulang.GeneralNominalCenteredSteps.State roles} {focus : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {key : Nat} (checked : Yulang.GeneralDeclarations.Checked registry)
  (one : Yulang.GeneralNominalCenteredHeadOutputs.Frame registry state focus key first)
  (two : Yulang.GeneralNominalCenteredHeadOutputs.Frame registry state focus key last) (name : Nat) :
  first.binder name = last.binder name
Yulang.GeneralDictionaryDefaultFrameSemantics209.body_iff {roles : Yulang.Roles.RoleDecls}
  {first last : Yulang.GeneralNominalCenters.Plan roles} {model : Yulang.GeneralNominalCommonBridge.Assignment}
  {registry : Yulang.GeneralDeclarations.Registry} {state : Yulang.GeneralNominalCenteredSteps.State roles}
  {focus : Yulang.GeneralSourceDictionaries.Occurrence roles} {key target : Nat}
  {body : Yulang.GeneralDictionaryAssociatedProvenance.Body} (checked : Yulang.GeneralDeclarations.Checked registry)
  (one : Yulang.GeneralNominalCenteredHeadOutputs.Frame registry state focus key first)
  (two : Yulang.GeneralNominalCenteredHeadOutputs.Frame registry state focus key last)
  (point :
    ∀ (index : Fin (roles focus.demand.role).arity),
      (focus.demand.arguments index).fst = (focus.demand.arguments index).snd)
  (firstHolds : first.input.Holds model) (lastHolds : last.input.Holds model) :
  Yulang.GeneralNominalCenteredHeadMatEffects.BodyHolds first target model body ↔
    Yulang.GeneralNominalCenteredHeadMatEffects.BodyHolds last target model body
Yulang.GeneralDictionaryDefaultFrameSemantics209.class_iff {roles : Yulang.Roles.RoleDecls}
  {first last : Yulang.GeneralNominalCenters.Plan roles} {model : Yulang.GeneralNominalCommonBridge.Assignment}
  {registry : Yulang.GeneralDeclarations.Registry} {state : Yulang.GeneralNominalCenteredSteps.State roles}
  {focus : Yulang.GeneralSourceDictionaries.Occurrence roles} {key : Nat}
  (checked : Yulang.GeneralDeclarations.Checked registry)
  (one : Yulang.GeneralNominalCenteredHeadOutputs.Frame registry state focus key first)
  (two : Yulang.GeneralNominalCenteredHeadOutputs.Frame registry state focus key last)
  (point :
    ∀ (index : Fin (roles focus.demand.role).arity),
      (focus.demand.arguments index).fst = (focus.demand.arguments index).snd)
  (firstHolds : first.input.Holds model) (lastHolds : last.input.Holds model) :
  Yulang.GeneralNominalCenteredHeadMatEffects.ClassEffects state focus first model ↔
    Yulang.GeneralNominalCenteredHeadMatEffects.ClassEffects state focus last model
Yulang.GeneralDictionaryDefaultFrameSemantics209.model_class_iff {roles : Yulang.Roles.RoleDecls}
  {first last : Yulang.GeneralNominalCenters.Plan roles} {model : Yulang.GeneralNominalCommonBridge.Assignment}
  {value : (Yulang.GeneralNominalCenteredHeadMatStepLocal.vocabulary roles).Registry}
  {focus : Yulang.GeneralSourceDictionaries.Occurrence roles} {key : Nat}
  {state : Yulang.GeneralNominalCenteredHeadMatStepJournal.State roles}
  (checked : (Yulang.GeneralDictionaryDefaultBoundary208.boundary roles).Checked value)
  (one :
    Yulang.GeneralNominalCenteredHeadOutputs.Frame (Yulang.GeneralNominalCenteredHeadAllocEncoding.registry value)
      state.core focus key first)
  (two :
    Yulang.GeneralNominalCenteredHeadOutputs.Frame (Yulang.GeneralNominalCenteredHeadAllocEncoding.registry value)
      state.core focus key last)
  (point :
    ∀ (index : Fin (roles focus.demand.role).arity),
      (focus.demand.arguments index).fst = (focus.demand.arguments index).snd)
  (valid : Yulang.GeneralNominalCenteredHeadMatStepJournal.Models state model) :
  Yulang.GeneralNominalCenteredHeadMatEffects.ClassEffects state.core focus first model ↔
    Yulang.GeneralNominalCenteredHeadMatEffects.ClassEffects state.core focus last model
Yulang.GeneralDictionaryDefaultHeadTransport209.similar_of_observations
  {model : Yulang.GeneralNominalCommonBridge.Assignment} {a b : Yulang.GeneralNominalRecursiveInspection.Origin}
  (agree :
    ∀ (value : Yulang.CommonNominalFullCarrier.Ty),
      Yulang.GeneralNominalRecursiveInspection.Observes model a value ↔
        Yulang.GeneralNominalRecursiveInspection.Observes model b value) :
  Yulang.GeneralNominalOriginAlias181.Similar model a b
Yulang.GeneralDictionaryDefaultHeadTransport209.head_similar {model : Yulang.GeneralNominalCommonBridge.Assignment}
  {a b : Yulang.GeneralNominalRecursiveInspection.Origin} {test : Yulang.GeneralNominalRecursiveInspection.Test}
  (similar : Yulang.GeneralNominalOriginAlias181.Similar model a b)
  (held : Yulang.GeneralNominalOriginTerms.Head model a test) : Yulang.GeneralNominalOriginTerms.Head model b test
Yulang.GeneralDictionaryDefaultHeadTransport209.actual_similar {model : Yulang.GeneralNominalCommonBridge.Assignment}
  {a b : Yulang.GeneralNominalRecursiveInspection.Origin} {x y : Nat}
  (similar : Yulang.GeneralNominalOriginAlias181.Similar model a b)
  (binders : Yulang.CommonNominalFullCarrier.Equivalent (model x).fst (model y).fst)
  (held : Yulang.GeneralNominalOriginTerms.Same model a (Yulang.GeneralNominalRecursiveInspection.Origin.source x)) :
  Yulang.GeneralNominalOriginTerms.Same model b (Yulang.GeneralNominalRecursiveInspection.Origin.source y)
Yulang.GeneralDictionaryDefaultHeadTransport209.append_iff {roles : Yulang.Roles.RoleDecls}
  {model : Yulang.GeneralNominalCommonBridge.Assignment} (plan : Yulang.GeneralNominalCenters.Plan roles)
  (one two : Yulang.GeneralNominalMaterialization.Schema) :
  plan.SchemaHolds (one.append two) model ↔ plan.SchemaHolds one model ∧ plan.SchemaHolds two model
Yulang.GeneralDictionaryDefaultHeadTransport209.tested_iff {roles : Yulang.Roles.RoleDecls}
  {model : Yulang.GeneralNominalCommonBridge.Assignment} (plan : Yulang.GeneralNominalCenters.Plan roles)
  (schema : Yulang.GeneralNominalMaterialization.Schema) (origin : Yulang.GeneralNominalRecursiveInspection.Origin)
  (test : Yulang.GeneralNominalRecursiveInspection.Test) :
  plan.SchemaHolds { variables := schema.variables, tests := (origin, test) :: schema.tests, unknown := schema.unknown }
      model ↔
    Yulang.GeneralNominalOriginTerms.Head model origin test ∧ plan.SchemaHolds schema model
Yulang.GeneralDictionaryDefaultHeadTransport209.schema_transport {roles : Yulang.Roles.RoleDecls}
  {first last : Yulang.GeneralNominalCenters.Plan roles} {model : Yulang.GeneralNominalCommonBridge.Assignment}
  {a b : Yulang.GeneralNominalRecursiveInspection.Origin} (query : Yulang.GeneralNominalInspection.Query)
  (similar : Yulang.GeneralNominalOriginAlias181.Similar model a b)
  (binders :
    ∀ (name : Nat),
      Yulang.CommonNominalFullCarrier.Equivalent (model (first.binder name)).fst (model (last.binder name)).fst)
  (held :
    first.SchemaHolds
      (Yulang.GeneralNominalMaterialization.schema query a Yulang.GeneralNominalMaterialization.Mode.actual) model) :
  last.SchemaHolds
    (Yulang.GeneralNominalMaterialization.schema query b Yulang.GeneralNominalMaterialization.Mode.actual) model
Yulang.GeneralDictionaryDefaultHeadTransport209.schemas_transport {roles : Yulang.Roles.RoleDecls}
  {first last : Yulang.GeneralNominalCenters.Plan roles} {model : Yulang.GeneralNominalCommonBridge.Assignment}
  {a b : Nat → Yulang.GeneralNominalRecursiveInspection.Origin} {offset : Nat}
  (queries : List Yulang.GeneralNominalInspection.Query)
  (similar : ∀ (index : Nat), Yulang.GeneralNominalOriginAlias181.Similar model (a index) (b index))
  (binders :
    ∀ (name : Nat),
      Yulang.CommonNominalFullCarrier.Equivalent (model (first.binder name)).fst (model (last.binder name)).fst)
  (held :
    first.SchemaHolds
      (Yulang.GeneralNominalMaterialization.schemas queries a Yulang.GeneralNominalMaterialization.Mode.actual offset)
      model) :
  last.SchemaHolds
    (Yulang.GeneralNominalMaterialization.schemas queries b Yulang.GeneralNominalMaterialization.Mode.actual offset)
    model
Yulang.GeneralDictionaryDefaultHeadTransport209.head_schema_transport {roles : Yulang.Roles.RoleDecls}
  {first last : Yulang.GeneralNominalCenters.Plan roles} {model : Yulang.GeneralNominalCommonBridge.Assignment}
  (declaration : first.packet.declaration = last.packet.declaration)
  (constructors : first.packet.context.state.constructors = last.packet.context.state.constructors)
  (interpretation : first.packet.context.interpretation = last.packet.context.interpretation)
  (centers :
    ∀ (index : Nat),
      Yulang.CommonNominalFullCarrier.Equivalent (model ((List.ofFn first.input.center)[index]?.getD 0)).fst
        (model ((List.ofFn last.input.center)[index]?.getD 0)).fst)
  (binders :
    ∀ (name : Nat),
      Yulang.CommonNominalFullCarrier.Equivalent (model (first.binder name)).fst (model (last.binder name)).fst)
  (held : first.SchemaHolds first.headSchema model) : last.SchemaHolds last.headSchema model
Yulang.GeneralDictionaryDefaultHeadTransport209.point_head_schema_transport {roles : Yulang.Roles.RoleDecls}
  {first last : Yulang.GeneralNominalCenters.Plan roles} {model : Yulang.GeneralNominalCommonBridge.Assignment}
  (declaration : first.packet.declaration = last.packet.declaration)
  (constructors : first.packet.context.state.constructors = last.packet.context.state.constructors)
  (interpretation : first.packet.context.interpretation = last.packet.context.interpretation)
  (occurrence : first.input.occurrence = last.input.occurrence)
  (point :
    ∀ (index : Fin (roles first.input.occurrence.demand.role).arity),
      (first.input.occurrence.demand.arguments index).fst = (first.input.occurrence.demand.arguments index).snd)
  (one : first.input.Holds model) (two : last.input.Holds model)
  (binders :
    ∀ (name : Nat),
      Yulang.CommonNominalFullCarrier.Equivalent (model (first.binder name)).fst (model (last.binder name)).fst)
  (held : first.SchemaHolds first.headSchema model) : last.SchemaHolds last.headSchema model
Yulang.GeneralDictionaryDefaultHeadTransport209.current_frame_schema {roles : Yulang.Roles.RoleDecls}
  {first last : Yulang.GeneralNominalCenters.Plan roles} {model : Yulang.GeneralNominalCommonBridge.Assignment}
  {registry : Yulang.GeneralDeclarations.Registry} {state : Yulang.GeneralNominalCenteredSteps.State roles}
  {focus : Yulang.GeneralSourceDictionaries.Occurrence roles} {key : Nat}
  (checked : Yulang.GeneralDeclarations.Checked registry)
  (one : Yulang.GeneralNominalCenteredHeadOutputs.Frame registry state focus key first)
  (two : Yulang.GeneralNominalCenteredHeadOutputs.Frame registry state focus key last)
  (point :
    ∀ (index : Fin (roles focus.demand.role).arity),
      (focus.demand.arguments index).fst = (focus.demand.arguments index).snd)
  (firstHolds : first.input.Holds model) (lastHolds : last.input.Holds model)
  (held : first.SchemaHolds first.headSchema model) : last.SchemaHolds last.headSchema model
Yulang.GeneralDictionaryDefaultObserved209.erase_report {before after : Yulang.GeneralNominalState.State}
  (refinement : Yulang.GeneralNominalRefinements.Refines before after)
  (report : Yulang.GeneralNominalRecursiveInspection.Report before) :
  Yulang.GeneralNominalReportErasure.erase after
      (Yulang.GeneralNominalSlotReport198.report refinement.base.embed report) =
    Yulang.GeneralNominalReportErasure.erase before report
Yulang.GeneralDictionaryDefaultObserved209.located_stored {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalCenteredHeadMatStepJournal.State roles}
  {historical : Yulang.GeneralNominalCenters.Plan roles}
  {value : (Yulang.GeneralNominalCenteredHeadMatStepLocal.vocabulary roles).Registry}
  {root : (Yulang.GeneralNominalCenteredHeadMatStepLocal.vocabulary roles).Demand}
  (reachable : Yulang.B4TargetV7.Reachable (Yulang.GeneralDictionaryDefaultBoundary208.boundary roles) value root state)
  (member : historical ∈ state.core.plans) :
  Yulang.GeneralNominalRecursiveCandidates.arguments historical.packet.context
      (Yulang.GeneralNominalCenteredHeadCandidates.inputs historical.packet.site.occurrence) =
    some historical.packet.bounds
Yulang.GeneralDictionaryDefaultObserved209.report_equal {roles : Yulang.Roles.RoleDecls}
  {current historical : Yulang.GeneralNominalCenters.Plan roles}
  (refinement : Yulang.GeneralNominalRefinements.Refines historical.packet.context.state current.packet.context.state)
  (interpretation : current.packet.context.interpretation = historical.packet.context.interpretation)
  (declaration : current.packet.declaration = historical.packet.declaration)
  (occurrence : current.packet.site.occurrence = historical.packet.site.occurrence)
  (oldLocated :
    Yulang.GeneralNominalRecursiveCandidates.arguments historical.packet.context
        (Yulang.GeneralNominalCenteredHeadCandidates.inputs historical.packet.site.occurrence) =
      some historical.packet.bounds)
  (currentLocated :
    Yulang.GeneralNominalRecursiveCandidates.arguments current.packet.context
        (Yulang.GeneralNominalCenteredHeadCandidates.inputs current.packet.site.occurrence) =
      some current.packet.bounds)
  (observed :
    Yulang.GeneralNominalRefinementTrace197.ObservedMany historical.packet.context.state
      (Yulang.GeneralNominalInspection.queries historical.packet.context.state historical.packet.context.interpretation
        historical.packet.declaration)
      historical.packet.bounds) :
  Yulang.GeneralNominalReportErasure.erase current.packet.context.state
      (Yulang.GeneralNominalPacketSupport.report current.packet) =
    Yulang.GeneralNominalReportErasure.erase historical.packet.context.state
      (Yulang.GeneralNominalPacketSupport.report historical.packet)
Yulang.GeneralDictionaryDefaultObserved209.reinspection_data {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalCenteredHeadMatStepJournal.State roles}
  {current historical : Yulang.GeneralNominalCenters.Plan roles}
  {value : (Yulang.GeneralNominalCenteredHeadMatStepLocal.vocabulary roles).Registry}
  {root : (Yulang.GeneralNominalCenteredHeadMatStepLocal.vocabulary roles).Demand}
  {focus : Yulang.GeneralSourceDictionaries.Occurrence roles} {key : Nat}
  (reachable : Yulang.B4TargetV7.Reachable (Yulang.GeneralDictionaryDefaultBoundary208.boundary roles) value root state)
  (frame :
    Yulang.GeneralNominalCenteredHeadOutputs.Frame (Yulang.GeneralNominalCenteredHeadAllocEncoding.registry value)
      state.core focus key current)
  (member : historical ∈ state.core.plans) (declaration : current.packet.declaration = historical.packet.declaration)
  (input : current.input = historical.input)
  (refinement : Yulang.GeneralNominalRefinements.Refines historical.packet.context.state current.packet.context.state)
  (observed :
    Yulang.GeneralNominalRefinementTrace197.ObservedMany historical.packet.context.state
      (Yulang.GeneralNominalInspection.queries historical.packet.context.state historical.packet.context.interpretation
        historical.packet.declaration)
      historical.packet.bounds) :
  Yulang.GeneralNominalCenteredHeadMatPlanData.Same current historical
Yulang.GeneralDictionaryDefaultObserved209.observed_stored {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalCenteredHeadMatStepJournal.State roles}
  {historical : Yulang.GeneralNominalCenters.Plan roles}
  {value : (Yulang.GeneralNominalCenteredHeadMatStepLocal.vocabulary roles).Registry}
  {root : (Yulang.GeneralNominalCenteredHeadMatStepLocal.vocabulary roles).Demand}
  (reachable : Yulang.B4TargetV7.Reachable (Yulang.GeneralDictionaryDefaultBoundary208.boundary roles) value root state)
  (member : historical ∈ state.core.plans)
  (shape :
    ∀ (query : Yulang.GeneralNominalInspection.Query),
      query ∈
          Yulang.GeneralNominalInspection.queries historical.packet.context.state
            historical.packet.context.interpretation historical.packet.declaration →
        Yulang.GeneralNominalFinishedObservation197.Syntax query) :
  Yulang.GeneralNominalRefinementTrace197.ObservedMany historical.packet.context.state
    (Yulang.GeneralNominalInspection.queries historical.packet.context.state historical.packet.context.interpretation
      historical.packet.declaration)
    historical.packet.bounds
Yulang.GeneralDictionaryDefaultObserved209.nominal_certificate {roles : Yulang.Roles.RoleDecls}
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
  (member : historical ∈ state.core.plans) (declaration : current.packet.declaration = historical.packet.declaration)
  (input : current.input = historical.input)
  (refinement : Yulang.GeneralNominalRefinements.Refines historical.packet.context.state current.packet.context.state)
  (shape :
    ∀ (query : Yulang.GeneralNominalInspection.Query),
      query ∈
          Yulang.GeneralNominalInspection.queries historical.packet.context.state
            historical.packet.context.interpretation historical.packet.declaration →
        Yulang.GeneralNominalFinishedObservation197.Syntax query)
  (valid : Yulang.GeneralNominalCenteredHeadMatStepJournal.Models state model) :
  Yulang.GeneralDictionaryTotalEvidence206.Certificate (Yulang.GeneralNominalCenteredHeadAllocEncoding.registry value)
    state.core model focus key current.packet.children current
Yulang.GeneralDictionaryDefaultObserved209.nominal_evidence_node {roles : Yulang.Roles.RoleDecls}
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
  (member : historical ∈ state.core.plans) (declaration : current.packet.declaration = historical.packet.declaration)
  (input : current.input = historical.input)
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
Yulang.GeneralDictionaryDefaultObserved209.nominal_generated_children {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalCenteredHeadMatStepJournal.State roles}
  {current historical : Yulang.GeneralNominalCenters.Plan roles}
  {value : (Yulang.GeneralNominalCenteredHeadMatStepLocal.vocabulary roles).Registry}
  {root : (Yulang.GeneralNominalCenteredHeadMatStepLocal.vocabulary roles).Demand}
  {focus : Yulang.GeneralSourceDictionaries.Occurrence roles} {key : Nat}
  {child : Yulang.GeneralSourceDictionaries.Occurrence roles}
  (reachable : Yulang.B4TargetV7.Reachable (Yulang.GeneralDictionaryDefaultBoundary208.boundary roles) value root state)
  (frame :
    Yulang.GeneralNominalCenteredHeadOutputs.Frame (Yulang.GeneralNominalCenteredHeadAllocEncoding.registry value)
      state.core focus key current)
  (member : historical ∈ state.core.plans) (declaration : current.packet.declaration = historical.packet.declaration)
  (input : current.input = historical.input)
  (refinement : Yulang.GeneralNominalRefinements.Refines historical.packet.context.state current.packet.context.state)
  (shape :
    ∀ (query : Yulang.GeneralNominalInspection.Query),
      query ∈
          Yulang.GeneralNominalInspection.queries historical.packet.context.state
            historical.packet.context.interpretation historical.packet.declaration →
        Yulang.GeneralNominalFinishedObservation197.Syntax query)
  (reached :
    focus = root ∨ (Yulang.GeneralDictionaryDefaultBoundary208.boundary roles).Generated value state root focus)
  (childMember : child ∈ current.packet.children) :
  (Yulang.GeneralDictionaryDefaultBoundary208.boundary roles).Generated value state root child
Yulang.GeneralDictionaryDefaultOutputBridge209.stored_visible {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalCenteredHeadMatStepJournal.State roles}
  {historical : Yulang.GeneralNominalCenters.Plan roles}
  {value : (Yulang.GeneralNominalCenteredHeadMatStepLocal.vocabulary roles).Registry}
  {root : (Yulang.GeneralNominalCenteredHeadMatStepLocal.vocabulary roles).Demand}
  (reachable : Yulang.B4TargetV7.Reachable (Yulang.GeneralDictionaryDefaultBoundary208.boundary roles) value root state)
  (present : historical ∈ state.core.plans) :
  historical.packet.declaration ∈ (Yulang.GeneralNominalCenteredHeadAllocEncoding.registry value).declarations
Yulang.GeneralDictionaryDefaultOutputBridge209.declaration_of_key {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalCenteredHeadMatStepJournal.State roles}
  {current historical : Yulang.GeneralNominalCenters.Plan roles}
  {value : (Yulang.GeneralNominalCenteredHeadMatStepLocal.vocabulary roles).Registry}
  {root : (Yulang.GeneralNominalCenteredHeadMatStepLocal.vocabulary roles).Demand}
  {focus : Yulang.GeneralSourceDictionaries.Occurrence roles} {key : Nat}
  (checked : (Yulang.GeneralDictionaryDefaultBoundary208.boundary roles).Checked value)
  (reachable : Yulang.B4TargetV7.Reachable (Yulang.GeneralDictionaryDefaultBoundary208.boundary roles) value root state)
  (frame :
    Yulang.GeneralNominalCenteredHeadOutputs.Frame (Yulang.GeneralNominalCenteredHeadAllocEncoding.registry value)
      state.core focus key current)
  (present : historical ∈ state.core.plans) (keyEq : historical.packet.declaration.id = key) :
  current.packet.declaration = historical.packet.declaration
Yulang.GeneralDictionaryDefaultOutputBridge209.default_class {roles : Yulang.Roles.RoleDecls}
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
  (present : historical ∈ state.core.plans) (keyEq : historical.packet.declaration.id = key)
  (occurrence : historical.packet.site.occurrence = focus)
  (point :
    ∀ (index : Fin (roles current.input.occurrence.demand.role).arity),
      (current.input.occurrence.demand.arguments index).fst = (current.input.occurrence.demand.arguments index).snd)
  (defaults :
    ∀ (output : Yulang.GeneralSourceState.Output),
      output ∈ Yulang.GeneralNominalCenteredHeadOutputs.requests state.core focus →
        ∀ (body : Yulang.GeneralDictionaryAssociatedProvenance.Body),
          Yulang.GeneralDictionaryAssociatedProvenance.lookup roles current.packet.declaration output.name = some body →
            ∃ role name term, body = Yulang.GeneralDictionaryAssociatedProvenance.Body.default role name term)
  (valid : Yulang.GeneralNominalCenteredHeadMatStepJournal.Models state model) :
  Yulang.GeneralNominalCenteredHeadMatEffects.ClassEffects state.core focus current model
Yulang.GeneralDictionaryDefaultOutputBridge209.default_certificate {roles : Yulang.Roles.RoleDecls}
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
  (present : historical ∈ state.core.plans) (keyEq : historical.packet.declaration.id = key)
  (occurrence : historical.packet.site.occurrence = focus)
  (point :
    ∀ (index : Fin (roles current.input.occurrence.demand.role).arity),
      (current.input.occurrence.demand.arguments index).fst = (current.input.occurrence.demand.arguments index).snd)
  (defaults :
    ∀ (output : Yulang.GeneralSourceState.Output),
      output ∈ Yulang.GeneralNominalCenteredHeadOutputs.requests state.core focus →
        ∀ (body : Yulang.GeneralDictionaryAssociatedProvenance.Body),
          Yulang.GeneralDictionaryAssociatedProvenance.lookup roles current.packet.declaration output.name = some body →
            ∃ role name term, body = Yulang.GeneralDictionaryAssociatedProvenance.Body.default role name term)
  (valid : Yulang.GeneralNominalCenteredHeadMatStepJournal.Models state model)
  (packet : Yulang.GeneralNominalCenteredHeadMatStepPackets.Holds current model) :
  Yulang.GeneralDictionaryTotalEvidence206.Certificate (Yulang.GeneralNominalCenteredHeadAllocEncoding.registry value)
    state.core model focus key current.packet.children current
Yulang.GeneralDictionaryDefaultPointTransport209.centers_equivalent {roles : Yulang.Roles.RoleDecls}
  {model : Yulang.GeneralNominalCommonBridge.Assignment} (first last : Yulang.GeneralNominalCenters.Site roles)
  (same : first.occurrence = last.occurrence)
  (point :
    ∀ (index : Fin (roles first.occurrence.demand.role).arity),
      (first.occurrence.demand.arguments index).fst = (first.occurrence.demand.arguments index).snd)
  (one : first.Holds model) (two : last.Holds model) (index : Nat) :
  Yulang.CommonNominalFullCarrier.Equivalent (model ((List.ofFn first.center)[index]?.getD 0)).fst
    (model ((List.ofFn last.center)[index]?.getD 0)).fst
Yulang.GeneralDictionaryDefaultPointTransport209.default_transport {roles : Yulang.Roles.RoleDecls}
  {model : Yulang.GeneralNominalCommonBridge.Assignment} {target role name : Nat} {term : Yulang.Roles.Term}
  {first last : Yulang.GeneralNominalCenters.Plan roles}
  (constructors : first.packet.registry.constructors = last.packet.registry.constructors)
  (interpretation : first.packet.context.interpretation = last.packet.context.interpretation)
  (same : first.input.occurrence = last.input.occurrence)
  (point :
    ∀ (index : Fin (roles first.input.occurrence.demand.role).arity),
      (first.input.occurrence.demand.arguments index).fst = (first.input.occurrence.demand.arguments index).snd)
  (one : first.input.Holds model) (two : last.input.Holds model) :
  Yulang.GeneralNominalCenteredHeadMatEffects.BodyHolds first target model
      (Yulang.GeneralDictionaryAssociatedProvenance.Body.default role name term) ↔
    Yulang.GeneralNominalCenteredHeadMatEffects.BodyHolds last target model
      (Yulang.GeneralDictionaryAssociatedProvenance.Body.default role name term)
Yulang.GeneralDictionaryDefaultPointTransport209.stored_default_output {roles : Yulang.Roles.RoleDecls}
  {model : Yulang.GeneralNominalCommonBridge.Assignment}
  {value : (Yulang.GeneralNominalCenteredHeadMatStepLocal.vocabulary roles).Registry}
  {root : (Yulang.GeneralNominalCenteredHeadMatStepLocal.vocabulary roles).Demand}
  {focus : Yulang.GeneralSourceDictionaries.Occurrence roles} {key : Nat} {output : Yulang.GeneralSourceState.Output}
  {role name : Nat} {term : Yulang.Roles.Term} {state : Yulang.GeneralNominalCenteredHeadMatStepJournal.State roles}
  {current historical : Yulang.GeneralNominalCenters.Plan roles}
  (reachable : Yulang.B4TargetV7.Reachable (Yulang.GeneralDictionaryDefaultBoundary208.boundary roles) value root state)
  (frame :
    Yulang.GeneralNominalCenteredHeadOutputs.Frame (Yulang.GeneralNominalCenteredHeadAllocEncoding.registry value)
      state.core focus key current)
  (present : historical ∈ state.core.plans) (declaration : current.packet.declaration = historical.packet.declaration)
  (occurrence : historical.packet.site.occurrence = focus)
  (point :
    ∀ (index : Fin (roles current.input.occurrence.demand.role).arity),
      (current.input.occurrence.demand.arguments index).fst = (current.input.occurrence.demand.arguments index).snd)
  (valid : Yulang.GeneralNominalCenteredHeadMatStepJournal.Models state model)
  (member : output ∈ Yulang.GeneralNominalCenteredHeadOutputs.requests state.core focus)
  (found :
    Yulang.GeneralDictionaryAssociatedProvenance.lookup roles current.packet.declaration output.name =
      some (Yulang.GeneralDictionaryAssociatedProvenance.Body.default role name term)) :
  Yulang.GeneralNominalCenteredHeadMatEffects.BodyHolds current output.target model
    (Yulang.GeneralDictionaryAssociatedProvenance.Body.default role name term)
Yulang.GeneralDictionaryDefaultReadback209.unique_readback {registry : Yulang.GeneralDeclarations.Registry}
  {roles✝ : Yulang.Roles.RoleDecls} {state : Yulang.GeneralNominalCenteredSteps.State roles✝}
  {model : Yulang.GeneralNominalCommonBridge.Assignment} {focus : Yulang.GeneralSourceDictionaries.Occurrence roles✝}
  {payload : Yulang.GeneralDictionaryReadback.Payload} (checked : Yulang.GeneralDeclarations.Checked registry)
  (given : Yulang.GeneralDictionaryTotalEvidence206.Evidence registry state model focus payload) :
  ∃ tree,
    (Yulang.GeneralSourceDictionaries.Readback focus payload tree ∧
        Yulang.GeneralSourceDictionaries.Evidence
          (Yulang.GeneralDictionaryTotalEvidence206.Instance registry state model) tree) ∧
      ∀ (other : Yulang.GeneralSourceDictionaries.Dictionary roles✝),
        Yulang.GeneralSourceDictionaries.Readback focus payload other →
          Yulang.GeneralSourceDictionaries.Evidence
              (Yulang.GeneralDictionaryTotalEvidence206.Instance registry state model) other →
            other = tree
Yulang.GeneralDictionaryDefaultReadback209.anyModel_functional {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {state : Yulang.GeneralNominalCenteredSteps.State roles}
  (checked : Yulang.GeneralDeclarations.Checked registry) :
  Yulang.GeneralDictionaryReadback.ChildrenFunctional
    (Yulang.GeneralDictionaryDefaultReadback209.AnyModelInstance registry state)
Yulang.GeneralDictionaryDefaultReadback209.model_independent_readback {registry : Yulang.GeneralDeclarations.Registry}
  {roles✝ : Yulang.Roles.RoleDecls} {focus : Yulang.GeneralSourceDictionaries.Occurrence roles✝}
  {payload : Yulang.CommonRoleOutermostResolver.Dictionary}
  {first last : Yulang.GeneralSourceDictionaries.Dictionary roles✝}
  {state : Yulang.GeneralNominalCenteredSteps.State roles✝}
  {model otherModel : Yulang.GeneralNominalCommonBridge.Assignment}
  (checked : Yulang.GeneralDeclarations.Checked registry)
  (one : Yulang.GeneralSourceDictionaries.Readback focus payload first)
  (two : Yulang.GeneralSourceDictionaries.Readback focus payload last)
  (firstEvidence :
    Yulang.GeneralSourceDictionaries.Evidence (Yulang.GeneralDictionaryTotalEvidence206.Instance registry state model)
      first)
  (lastEvidence :
    Yulang.GeneralSourceDictionaries.Evidence
      (Yulang.GeneralDictionaryTotalEvidence206.Instance registry state otherModel) last) :
  first = last
Yulang.GeneralDictionaryDefaultReadback209.node_iff {registry : Yulang.GeneralDeclarations.Registry}
  {roles✝ : Yulang.Roles.RoleDecls} {state : Yulang.GeneralNominalCenteredSteps.State roles✝}
  {model : Yulang.GeneralNominalCommonBridge.Assignment} {focus : Yulang.GeneralSourceDictionaries.Occurrence roles✝}
  {key : Nat} {payloads : List Yulang.CommonRoleOutermostResolver.Dictionary} :
  Yulang.GeneralDictionaryTotalEvidence206.Evidence registry state model focus
      (Yulang.CommonRoleOutermostResolver.Dictionary.node key payloads) ↔
    ∃ children,
      Yulang.GeneralDictionaryTotalEvidence206.Instance registry state model focus key children ∧
        Yulang.CommonRoleOutermostResolver.All₂ (Yulang.GeneralDictionaryTotalEvidence206.Evidence registry state model)
          children payloads
Yulang.GeneralDictionaryDefaultReadback209.node_current_frame_iff {registry : Yulang.GeneralDeclarations.Registry}
  {roles✝ : Yulang.Roles.RoleDecls} {state : Yulang.GeneralNominalCenteredSteps.State roles✝}
  {focus : Yulang.GeneralSourceDictionaries.Occurrence roles✝} {key : Nat}
  {plan : Yulang.GeneralNominalCenters.Plan roles✝} {model : Yulang.GeneralNominalCommonBridge.Assignment}
  {payloads : List Yulang.CommonRoleOutermostResolver.Dictionary}
  (checked : Yulang.GeneralDeclarations.Checked registry)
  (frame : Yulang.GeneralNominalCenteredHeadOutputs.Frame registry state focus key plan) :
  Yulang.GeneralDictionaryTotalEvidence206.Evidence registry state model focus
      (Yulang.CommonRoleOutermostResolver.Dictionary.node key payloads) ↔
    Yulang.GeneralDictionaryTotalEvidence206.Instance registry state model focus key plan.packet.children ∧
      Yulang.CommonRoleOutermostResolver.All₂ (Yulang.GeneralDictionaryTotalEvidence206.Evidence registry state model)
        plan.packet.children payloads
Yulang.GeneralDictionaryDefaultReinspection209.body_same {roles : Yulang.Roles.RoleDecls}
  {current historical : Yulang.GeneralNominalCenters.Plan roles} {model : Yulang.GeneralNominalCommonBridge.Assignment}
  {target : Nat} {body : Yulang.GeneralDictionaryAssociatedProvenance.Body}
  (same : Yulang.GeneralNominalCenteredHeadMatPlanData.Same current historical) :
  Yulang.GeneralNominalCenteredHeadMatEffects.BodyHolds current target model body ↔
    Yulang.GeneralNominalCenteredHeadMatEffects.BodyHolds historical target model body
Yulang.GeneralDictionaryDefaultReinspection209.effects_same {roles : Yulang.Roles.RoleDecls}
  {current historical : Yulang.GeneralNominalCenters.Plan roles} {model : Yulang.GeneralNominalCommonBridge.Assignment}
  {core : Yulang.GeneralNominalCenteredSteps.State roles} {focus : Yulang.GeneralSourceDictionaries.Occurrence roles}
  (same : Yulang.GeneralNominalCenteredHeadMatPlanData.Same current historical) :
  Yulang.GeneralNominalCenteredHeadMatEffects.ClassEffects core focus current model ↔
    Yulang.GeneralNominalCenteredHeadMatEffects.ClassEffects core focus historical model
Yulang.GeneralDictionaryDefaultReinspection209.packet_reinspect {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalCenteredHeadMatStepJournal.State roles}
  {current historical : Yulang.GeneralNominalCenters.Plan roles} {model : Yulang.GeneralNominalCommonBridge.Assignment}
  {value : Yulang.GeneralDeclarations.Registry} {focus : Yulang.GeneralSourceDictionaries.Occurrence roles} {key : Nat}
  (same : Yulang.GeneralNominalCenteredHeadMatPlanData.Same current historical)
  (frame : Yulang.GeneralNominalCenteredHeadOutputs.Frame value state.core focus key current)
  (valid : Yulang.GeneralNominalCenteredHeadMatStepJournal.Models state model)
  (old : Yulang.GeneralNominalCenteredHeadMatStepPackets.Holds historical model) :
  Yulang.GeneralNominalCenteredHeadMatStepPackets.Holds current model
Yulang.GeneralDictionaryDefaultReinspection209.certificate {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalCenteredHeadMatStepJournal.State roles}
  {current historical : Yulang.GeneralNominalCenters.Plan roles} {model : Yulang.GeneralNominalCommonBridge.Assignment}
  {value : (Yulang.GeneralNominalCenteredHeadMatStepLocal.vocabulary roles).Registry}
  {root : (Yulang.GeneralNominalCenteredHeadMatStepLocal.vocabulary roles).Demand}
  {focus : Yulang.GeneralSourceDictionaries.Occurrence roles} {key : Nat}
  (checked : (Yulang.GeneralDictionaryDefaultBoundary208.boundary roles).Checked value)
  (reachable : Yulang.B4TargetV7.Reachable (Yulang.GeneralDictionaryDefaultBoundary208.boundary roles) value root state)
  (frame :
    Yulang.GeneralNominalCenteredHeadOutputs.Frame (Yulang.GeneralNominalCenteredHeadAllocEncoding.registry value)
      state.core focus key current)
  (present : historical ∈ state.core.plans)
  (same : Yulang.GeneralNominalCenteredHeadMatPlanData.Same current historical)
  (valid : Yulang.GeneralNominalCenteredHeadMatStepJournal.Models state model) :
  Yulang.GeneralDictionaryTotalEvidence206.Certificate (Yulang.GeneralNominalCenteredHeadAllocEncoding.registry value)
    state.core model focus key current.packet.children current
Yulang.GeneralDictionaryDefaultReinspection209.evidence_node {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalCenteredHeadMatStepJournal.State roles}
  {current historical : Yulang.GeneralNominalCenters.Plan roles} {model : Yulang.GeneralNominalCommonBridge.Assignment}
  {value : (Yulang.GeneralNominalCenteredHeadMatStepLocal.vocabulary roles).Registry}
  {root : (Yulang.GeneralNominalCenteredHeadMatStepLocal.vocabulary roles).Demand}
  {focus : Yulang.GeneralSourceDictionaries.Occurrence roles} {key : Nat}
  {dictionaries : List Yulang.GeneralDictionaryReadback.Payload}
  (checked : (Yulang.GeneralDictionaryDefaultBoundary208.boundary roles).Checked value)
  (reachable : Yulang.B4TargetV7.Reachable (Yulang.GeneralDictionaryDefaultBoundary208.boundary roles) value root state)
  (frame :
    Yulang.GeneralNominalCenteredHeadOutputs.Frame (Yulang.GeneralNominalCenteredHeadAllocEncoding.registry value)
      state.core focus key current)
  (present : historical ∈ state.core.plans)
  (same : Yulang.GeneralNominalCenteredHeadMatPlanData.Same current historical)
  (valid : Yulang.GeneralNominalCenteredHeadMatStepJournal.Models state model)
  (given :
    Yulang.CommonRoleOutermostResolver.All₂
      (Yulang.GeneralDictionaryTotalEvidence206.Evidence (Yulang.GeneralNominalCenteredHeadAllocEncoding.registry value)
        state.core model)
      current.packet.children dictionaries) :
  Yulang.GeneralDictionaryTotalEvidence206.Evidence (Yulang.GeneralNominalCenteredHeadAllocEncoding.registry value)
    state.core model focus (Yulang.CommonRoleOutermostResolver.Dictionary.node key dictionaries)
Yulang.GeneralDictionaryDefaultReinspection209.generated_children {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalCenteredHeadMatStepJournal.State roles}
  {current historical : Yulang.GeneralNominalCenters.Plan roles}
  {value : (Yulang.GeneralNominalCenteredHeadMatStepLocal.vocabulary roles).Registry}
  {root : (Yulang.GeneralNominalCenteredHeadMatStepLocal.vocabulary roles).Demand}
  {focus : Yulang.GeneralSourceDictionaries.Occurrence roles} {key : Nat}
  {child : Yulang.GeneralSourceDictionaries.Occurrence roles}
  (reachable : Yulang.B4TargetV7.Reachable (Yulang.GeneralDictionaryDefaultBoundary208.boundary roles) value root state)
  (frame :
    Yulang.GeneralNominalCenteredHeadOutputs.Frame (Yulang.GeneralNominalCenteredHeadAllocEncoding.registry value)
      state.core focus key current)
  (present : historical ∈ state.core.plans)
  (same : Yulang.GeneralNominalCenteredHeadMatPlanData.Same current historical)
  (reached :
    focus = root ∨ (Yulang.GeneralDictionaryDefaultBoundary208.boundary roles).Generated value state root focus)
  (member : child ∈ current.packet.children) :
  (Yulang.GeneralDictionaryDefaultBoundary208.boundary roles).Generated value state root child
Yulang.GeneralDictionaryDefaultReplayExamples209.total_at_center (name : Nat) :
  Yulang.GeneralNominalCenteredHeadMatStepPackets.Holds
    (Yulang.GeneralDictionaryDefaultTransportExamples209.pointPlan name)
    Yulang.GeneralDictionaryDefaultGap206Source.model
Yulang.GeneralDictionaryDefaultReplayExamples209.distinct_inputs :
  (Yulang.GeneralDictionaryDefaultTransportExamples209.pointPlan 1).input ≠
    (Yulang.GeneralDictionaryDefaultTransportExamples209.pointPlan 2).input
Yulang.GeneralDictionaryDefaultReplayExamples209.replay_one_to_two :
  Yulang.GeneralNominalCenteredHeadMatStepPackets.Holds
    (Yulang.GeneralDictionaryDefaultSemanticReplay209.recenter
      (Yulang.GeneralDictionaryDefaultTransportExamples209.pointPlan 1)
      (Yulang.GeneralDictionaryDefaultTransportExamples209.pointSite 2) ⋯)
    Yulang.GeneralDictionaryDefaultGap206Source.model
Yulang.GeneralDictionaryDefaultReplayExamples209.distinct_total_packets :
  (Yulang.GeneralDictionaryDefaultTransportExamples209.pointPlan 1).input ≠
      (Yulang.GeneralDictionaryDefaultTransportExamples209.pointPlan 2).input ∧
    Yulang.GeneralNominalCenteredHeadMatStepPackets.Holds
        (Yulang.GeneralDictionaryDefaultTransportExamples209.pointPlan 1)
        Yulang.GeneralDictionaryDefaultGap206Source.model ∧
      Yulang.GeneralNominalCenteredHeadMatStepPackets.Holds
        (Yulang.GeneralDictionaryDefaultTransportExamples209.pointPlan 2)
        Yulang.GeneralDictionaryDefaultGap206Source.model
Yulang.GeneralDictionaryDefaultSemanticReplay209.recenter_holds {roles : Yulang.Roles.RoleDecls}
  {historical : Yulang.GeneralNominalCenters.Plan roles} {model : Yulang.GeneralNominalCommonBridge.Assignment}
  (site : Yulang.GeneralNominalCenters.Site roles) (same : site.occurrence = historical.packet.site.occurrence)
  (point :
    ∀ (index : Fin (roles historical.input.occurrence.demand.role).arity),
      (historical.input.occurrence.demand.arguments index).fst =
        (historical.input.occurrence.demand.arguments index).snd)
  (center : site.Holds model) (old : Yulang.GeneralNominalCenteredHeadMatStepPackets.Holds historical model) :
  Yulang.GeneralNominalCenteredHeadMatStepPackets.Holds
    (Yulang.GeneralDictionaryDefaultSemanticReplay209.recenter historical site same) model
Yulang.GeneralDictionaryDefaultSemanticReplay209.recenter_class {roles : Yulang.Roles.RoleDecls}
  {historical : Yulang.GeneralNominalCenters.Plan roles} {model : Yulang.GeneralNominalCommonBridge.Assignment}
  {core : Yulang.GeneralNominalCenteredSteps.State roles} {focus : Yulang.GeneralSourceDictionaries.Occurrence roles}
  (site : Yulang.GeneralNominalCenters.Site roles) (same : site.occurrence = historical.packet.site.occurrence)
  (point :
    ∀ (index : Fin (roles historical.input.occurrence.demand.role).arity),
      (historical.input.occurrence.demand.arguments index).fst =
        (historical.input.occurrence.demand.arguments index).snd)
  (center : site.Holds model) (input : historical.input.Holds model) :
  Yulang.GeneralNominalCenteredHeadMatEffects.ClassEffects core focus historical model ↔
    Yulang.GeneralNominalCenteredHeadMatEffects.ClassEffects core focus
      (Yulang.GeneralDictionaryDefaultSemanticReplay209.recenter historical site same) model
Yulang.GeneralDictionaryDefaultSemanticReplay209.recentered_data {roles : Yulang.Roles.RoleDecls}
  {current historical : Yulang.GeneralNominalCenters.Plan roles}
  {value : (Yulang.GeneralNominalCenteredHeadMatStepLocal.vocabulary roles).Registry}
  {root : (Yulang.GeneralNominalCenteredHeadMatStepLocal.vocabulary roles).Demand}
  {focus : Yulang.GeneralSourceDictionaries.Occurrence roles} {key : Nat}
  {state : Yulang.GeneralNominalCenteredHeadMatStepJournal.State roles}
  (reachable : Yulang.B4TargetV7.Reachable (Yulang.GeneralDictionaryDefaultBoundary208.boundary roles) value root state)
  (frame :
    Yulang.GeneralNominalCenteredHeadOutputs.Frame (Yulang.GeneralNominalCenteredHeadAllocEncoding.registry value)
      state.core focus key current)
  (member : historical ∈ state.core.plans) (declaration : current.packet.declaration = historical.packet.declaration)
  (same : current.input.occurrence = historical.packet.site.occurrence)
  (report :
    Yulang.GeneralNominalReportErasure.erase current.packet.context.state
        (Yulang.GeneralNominalPacketSupport.report current.packet) =
      Yulang.GeneralNominalReportErasure.erase historical.packet.context.state
        (Yulang.GeneralNominalPacketSupport.report historical.packet)) :
  Yulang.GeneralNominalCenteredHeadMatPlanData.Same current
    (Yulang.GeneralDictionaryDefaultSemanticReplay209.recenter historical current.input same)
Yulang.GeneralDictionaryDefaultSemanticReplay209.certificate {roles : Yulang.Roles.RoleDecls}
  {current historical : Yulang.GeneralNominalCenters.Plan roles} {model : Yulang.GeneralNominalCommonBridge.Assignment}
  {value : (Yulang.GeneralNominalCenteredHeadMatStepLocal.vocabulary roles).Registry}
  {root : (Yulang.GeneralNominalCenteredHeadMatStepLocal.vocabulary roles).Demand}
  {focus : Yulang.GeneralSourceDictionaries.Occurrence roles} {key : Nat}
  {state : Yulang.GeneralNominalCenteredHeadMatStepJournal.State roles}
  (checked : (Yulang.GeneralDictionaryDefaultBoundary208.boundary roles).Checked value)
  (reachable : Yulang.B4TargetV7.Reachable (Yulang.GeneralDictionaryDefaultBoundary208.boundary roles) value root state)
  (frame :
    Yulang.GeneralNominalCenteredHeadOutputs.Frame (Yulang.GeneralNominalCenteredHeadAllocEncoding.registry value)
      state.core focus key current)
  (member : historical ∈ state.core.plans) (keyEq : historical.packet.declaration.id = key)
  (occurrence : historical.packet.site.occurrence = focus)
  (point :
    ∀ (index : Fin (roles focus.demand.role).arity),
      (focus.demand.arguments index).fst = (focus.demand.arguments index).snd)
  (report :
    Yulang.GeneralNominalReportErasure.erase current.packet.context.state
        (Yulang.GeneralNominalPacketSupport.report current.packet) =
      Yulang.GeneralNominalReportErasure.erase historical.packet.context.state
        (Yulang.GeneralNominalPacketSupport.report historical.packet))
  (valid : Yulang.GeneralNominalCenteredHeadMatStepJournal.Models state model) :
  Yulang.GeneralDictionaryTotalEvidence206.Certificate (Yulang.GeneralNominalCenteredHeadAllocEncoding.registry value)
    state.core model focus key current.packet.children current
Yulang.GeneralDictionaryDefaultSemanticReplay209.nominal_report {roles : Yulang.Roles.RoleDecls}
  {current historical : Yulang.GeneralNominalCenters.Plan roles}
  {value : (Yulang.GeneralNominalCenteredHeadMatStepLocal.vocabulary roles).Registry}
  {root : (Yulang.GeneralNominalCenteredHeadMatStepLocal.vocabulary roles).Demand}
  {focus : Yulang.GeneralSourceDictionaries.Occurrence roles} {key : Nat}
  {state : Yulang.GeneralNominalCenteredHeadMatStepJournal.State roles}
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
        Yulang.GeneralNominalFinishedObservation197.Syntax query) :
  Yulang.GeneralNominalReportErasure.erase current.packet.context.state
      (Yulang.GeneralNominalPacketSupport.report current.packet) =
    Yulang.GeneralNominalReportErasure.erase historical.packet.context.state
      (Yulang.GeneralNominalPacketSupport.report historical.packet)
Yulang.GeneralDictionaryDefaultSemanticReplay209.nominal_certificate {roles : Yulang.Roles.RoleDecls}
  {current historical : Yulang.GeneralNominalCenters.Plan roles} {model : Yulang.GeneralNominalCommonBridge.Assignment}
  {value : (Yulang.GeneralNominalCenteredHeadMatStepLocal.vocabulary roles).Registry}
  {root : (Yulang.GeneralNominalCenteredHeadMatStepLocal.vocabulary roles).Demand}
  {focus : Yulang.GeneralSourceDictionaries.Occurrence roles} {key : Nat}
  {state : Yulang.GeneralNominalCenteredHeadMatStepJournal.State roles}
  (checked : (Yulang.GeneralDictionaryDefaultBoundary208.boundary roles).Checked value)
  (reachable : Yulang.B4TargetV7.Reachable (Yulang.GeneralDictionaryDefaultBoundary208.boundary roles) value root state)
  (frame :
    Yulang.GeneralNominalCenteredHeadOutputs.Frame (Yulang.GeneralNominalCenteredHeadAllocEncoding.registry value)
      state.core focus key current)
  (member : historical ∈ state.core.plans) (keyEq : historical.packet.declaration.id = key)
  (occurrence : historical.packet.site.occurrence = focus)
  (point :
    ∀ (index : Fin (roles focus.demand.role).arity),
      (focus.demand.arguments index).fst = (focus.demand.arguments index).snd)
  (refinement : Yulang.GeneralNominalRefinements.Refines historical.packet.context.state current.packet.context.state)
  (shape :
    ∀ (query : Yulang.GeneralNominalInspection.Query),
      query ∈
          Yulang.GeneralNominalInspection.queries historical.packet.context.state
            historical.packet.context.interpretation historical.packet.declaration →
        Yulang.GeneralNominalFinishedObservation197.Syntax query)
  (valid : Yulang.GeneralNominalCenteredHeadMatStepJournal.Models state model) :
  Yulang.GeneralDictionaryTotalEvidence206.Certificate (Yulang.GeneralNominalCenteredHeadAllocEncoding.registry value)
    state.core model focus key current.packet.children current
Yulang.GeneralDictionaryDefaultSemanticReplay209.nominal_evidence_node {roles : Yulang.Roles.RoleDecls}
  {current historical : Yulang.GeneralNominalCenters.Plan roles} {model : Yulang.GeneralNominalCommonBridge.Assignment}
  {value : (Yulang.GeneralNominalCenteredHeadMatStepLocal.vocabulary roles).Registry}
  {root : (Yulang.GeneralNominalCenteredHeadMatStepLocal.vocabulary roles).Demand}
  {focus : Yulang.GeneralSourceDictionaries.Occurrence roles} {key : Nat}
  {dictionaries : List Yulang.GeneralDictionaryReadback.Payload}
  {state : Yulang.GeneralNominalCenteredHeadMatStepJournal.State roles}
  (checked : (Yulang.GeneralDictionaryDefaultBoundary208.boundary roles).Checked value)
  (reachable : Yulang.B4TargetV7.Reachable (Yulang.GeneralDictionaryDefaultBoundary208.boundary roles) value root state)
  (frame :
    Yulang.GeneralNominalCenteredHeadOutputs.Frame (Yulang.GeneralNominalCenteredHeadAllocEncoding.registry value)
      state.core focus key current)
  (member : historical ∈ state.core.plans) (keyEq : historical.packet.declaration.id = key)
  (occurrence : historical.packet.site.occurrence = focus)
  (point :
    ∀ (index : Fin (roles focus.demand.role).arity),
      (focus.demand.arguments index).fst = (focus.demand.arguments index).snd)
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
Yulang.GeneralDictionaryDefaultSemanticReplay209.generated_children {roles : Yulang.Roles.RoleDecls}
  {current historical : Yulang.GeneralNominalCenters.Plan roles}
  {value : (Yulang.GeneralNominalCenteredHeadMatStepLocal.vocabulary roles).Registry}
  {root : (Yulang.GeneralNominalCenteredHeadMatStepLocal.vocabulary roles).Demand}
  {focus : Yulang.GeneralSourceDictionaries.Occurrence roles} {key : Nat}
  {child : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {state : Yulang.GeneralNominalCenteredHeadMatStepJournal.State roles}
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
  (reached :
    focus = root ∨ (Yulang.GeneralDictionaryDefaultBoundary208.boundary roles).Generated value state root focus)
  (childMember : child ∈ current.packet.children) :
  (Yulang.GeneralDictionaryDefaultBoundary208.boundary roles).Generated value state root child
Yulang.GeneralDictionaryDefaultSemanticReplay209.nominal_generated_children {roles : Yulang.Roles.RoleDecls}
  {current historical : Yulang.GeneralNominalCenters.Plan roles}
  {value : (Yulang.GeneralNominalCenteredHeadMatStepLocal.vocabulary roles).Registry}
  {root : (Yulang.GeneralNominalCenteredHeadMatStepLocal.vocabulary roles).Demand}
  {focus : Yulang.GeneralSourceDictionaries.Occurrence roles} {key : Nat}
  {child : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {state : Yulang.GeneralNominalCenteredHeadMatStepJournal.State roles}
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
  (reached :
    focus = root ∨ (Yulang.GeneralDictionaryDefaultBoundary208.boundary roles).Generated value state root focus)
  (childMember : child ∈ current.packet.children) :
  (Yulang.GeneralDictionaryDefaultBoundary208.boundary roles).Generated value state root child
Yulang.GeneralDictionaryDefaultTransportExamples209.point_holds (name : Nat) :
  (Yulang.GeneralDictionaryDefaultTransportExamples209.pointSite name).Holds
    Yulang.GeneralDictionaryDefaultGap206Source.model
Yulang.GeneralDictionaryDefaultTransportExamples209.distinct_centers :
  (Yulang.GeneralDictionaryDefaultTransportExamples209.pointSite 1).center 0 ≠
    (Yulang.GeneralDictionaryDefaultTransportExamples209.pointSite 2).center 0
Yulang.GeneralDictionaryDefaultTransportExamples209.point_default (name : Nat) :
  Yulang.GeneralNominalCenteredHeadMatEffects.BodyHolds
    (Yulang.GeneralDictionaryDefaultTransportExamples209.pointPlan name) 0
    Yulang.GeneralDictionaryDefaultGap206Source.model
    (Yulang.GeneralDictionaryAssociatedProvenance.Body.default 0 0 (Yulang.Roles.Term.var 0))
Yulang.GeneralDictionaryDefaultTransportExamples209.distinct_default_transport :
  Yulang.GeneralNominalCenteredHeadMatEffects.BodyHolds
      (Yulang.GeneralDictionaryDefaultTransportExamples209.pointPlan 1) 0
      Yulang.GeneralDictionaryDefaultGap206Source.model
      (Yulang.GeneralDictionaryAssociatedProvenance.Body.default 0 0 (Yulang.Roles.Term.var 0)) ↔
    Yulang.GeneralNominalCenteredHeadMatEffects.BodyHolds
      (Yulang.GeneralDictionaryDefaultTransportExamples209.pointPlan 2) 0
      Yulang.GeneralDictionaryDefaultGap206Source.model
      (Yulang.GeneralDictionaryAssociatedProvenance.Body.default 0 0 (Yulang.Roles.Term.var 0))
Yulang.GeneralDictionaryDefaultTransportExamples209.interval_bottom_holds :
  (Yulang.GeneralDictionaryDefaultTransportExamples209.intervalSite 0).Holds
    Yulang.GeneralDictionaryDefaultTransportExamples209.intervalModel
Yulang.GeneralDictionaryDefaultTransportExamples209.interval_int_holds :
  (Yulang.GeneralDictionaryDefaultTransportExamples209.intervalSite 1).Holds
    Yulang.GeneralDictionaryDefaultTransportExamples209.intervalModel
Yulang.GeneralDictionaryDefaultTransportExamples209.interval_not_point :
  ¬∀
      (index :
        Fin
          (Yulang.GeneralDictionaryDefaultGap206Source.roles
              Yulang.GeneralDictionaryDefaultTransportExamples209.intervalRoot.demand.role).arity),
      (Yulang.GeneralDictionaryDefaultTransportExamples209.intervalRoot.demand.arguments index).fst =
        (Yulang.GeneralDictionaryDefaultTransportExamples209.intervalRoot.demand.arguments index).snd
Yulang.GeneralDictionaryDefaultTransportExamples209.interval_default_bottom :
  Yulang.GeneralNominalCenteredHeadMatEffects.BodyHolds
    (Yulang.GeneralDictionaryDefaultTransportExamples209.intervalPlan 0) 0
    Yulang.GeneralDictionaryDefaultTransportExamples209.intervalModel
    (Yulang.GeneralDictionaryAssociatedProvenance.Body.default 0 0 (Yulang.Roles.Term.var 0))
Yulang.GeneralDictionaryDefaultTransportExamples209.interval_default_int_false :
  ¬Yulang.GeneralNominalCenteredHeadMatEffects.BodyHolds
      (Yulang.GeneralDictionaryDefaultTransportExamples209.intervalPlan 1) 0
      Yulang.GeneralDictionaryDefaultTransportExamples209.intervalModel
      (Yulang.GeneralDictionaryAssociatedProvenance.Body.default 0 0 (Yulang.Roles.Term.var 0))
Yulang.GeneralDictionaryDefaultTransportExamples209.point_premise_necessary :
  (Yulang.GeneralDictionaryDefaultTransportExamples209.intervalSite 0).Holds
      Yulang.GeneralDictionaryDefaultTransportExamples209.intervalModel ∧
    (Yulang.GeneralDictionaryDefaultTransportExamples209.intervalSite 1).Holds
        Yulang.GeneralDictionaryDefaultTransportExamples209.intervalModel ∧
      Yulang.GeneralNominalCenteredHeadMatEffects.BodyHolds
          (Yulang.GeneralDictionaryDefaultTransportExamples209.intervalPlan 0) 0
          Yulang.GeneralDictionaryDefaultTransportExamples209.intervalModel
          (Yulang.GeneralDictionaryAssociatedProvenance.Body.default 0 0 (Yulang.Roles.Term.var 0)) ∧
        ¬Yulang.GeneralNominalCenteredHeadMatEffects.BodyHolds
            (Yulang.GeneralDictionaryDefaultTransportExamples209.intervalPlan 1) 0
            Yulang.GeneralDictionaryDefaultTransportExamples209.intervalModel
            (Yulang.GeneralDictionaryAssociatedProvenance.Body.default 0 0 (Yulang.Roles.Term.var 0))

```
