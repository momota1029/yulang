import Yulang.GeneralDictionaryGroundCopy218SaturatedState

set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralDictionaryGroundCopy218SaturatedParent
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters CommonNominalFullCarrier
open GeneralDictionaryGroundCopy218Source
open GeneralDictionaryGroundCopy218Install (declaration declaration_checked plan childSite clause)
open GeneralDictionaryGroundCopy218Reobserve
open GeneralDictionaryGroundCopy218Reinstall (newPlan newPacket newChild reinstalled)
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralNominalCenteredHeadMatStepJournal
open GeneralNominalCommonBridge (Assignment)

abbrev contextFor (allocated : List GeneralNominalIdentities.Origin) (reserved : List Nat)
    (ordinary : List (PresenceNormalForm.Atom Nat)) : GeneralNominalCandidates.Context :=
  ⟨pointExtended allocated reserved ordinary,interpretation⟩

abbrev packetFor (allocated : List GeneralNominalIdentities.Origin) (reserved : List Nat)
    (ordinary : List (PresenceNormalForm.Atom Nat)) : GeneralNominalSaturationState.Packet roles :=
  ⟨registry,contextFor allocated reserved ordinary,GeneralNominalDemandMerging.pointSite root,
    declaration,declaration_checked,[(6,6)]⟩

abbrev planFor (allocated : List GeneralNominalIdentities.Origin) (reserved : List Nat)
    (ordinary : List (PresenceNormalForm.Atom Nat)) : Plan roles :=
  ⟨packetFor allocated reserved ordinary,plan.input,rfl⟩

theorem query (allocated reserved ordinary) :
    GeneralNominalInspection.queries (contextFor allocated reserved ordinary).state interpretation declaration =
      [.nominal 5 [.variables [0],.variables [1]]] := by
  simp [GeneralNominalInspection.queries,Declaration.normalHead,
    GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
    GeneralNominalInspection.translate,interpretation,declaration,GeneralNominalCenteredHeadAllocEncoding.declaration]

theorem report_exact (allocated reserved ordinary) : report (contextFor allocated reserved ordinary) declaration [(6,6)] =
    { inspected := [(6,6)], checked := [(6,6),(6,6),(4,4),(5,5)],
      captures := [⟨0,(4,4),some (.nominal (.source 6) 5 0)⟩,
        ⟨1,(5,5),some (.nominal (.source 6) 5 1)⟩],
      anchors := [(.nominal (.source 6) 5 0,(4,4)),(.nominal (.source 6) 5 1,(5,5))] } := by
  have sub : inspectMany (contextFor allocated reserved ordinary).state [.variables [0],.variables [1]] [(4,4),(5,5)]
      (fun index => some (.nominal (.source 6) 5 index)) 0 =
      { captures := [⟨0,(4,4),some (.nominal (.source 6) 5 0)⟩,
          ⟨1,(5,5),some (.nominal (.source 6) 5 1)⟩],
        checked := [(4,4),(5,5)],
        anchors := [(.nominal (.source 6) 5 0,(4,4)),(.nominal (.source 6) 5 1,(5,5))] } := by
    simp [inspectMany,inspect,Report.append]
  unfold report
  rw [query]
  simp [inspectMany,inspect,typeArguments,Report.append,Report.visit]
  exact ⟨congrArg Report.captures sub,congrArg Report.inspected sub,congrArg Report.checked sub,
    congrArg Report.blocked sub,congrArg Report.conflicts sub,congrArg Report.arity sub,
    congrArg Report.anchors sub,congrArg Report.tests sub⟩

theorem bindings_exact (allocated reserved ordinary) : (packetFor allocated reserved ordinary).bindings = [(0,4,4),(1,5,5)] := by
  change bindings _ (report (contextFor allocated reserved ordinary) declaration [(6,6)]) = _
  rw [report_exact]; rfl

theorem capture_same (allocated reserved ordinary) :
    GeneralNominalPacketSupport.capture (packetFor allocated reserved ordinary) =
      GeneralNominalPacketSupport.capture newPacket := by
  unfold GeneralNominalPacketSupport.capture
  rw [bindings_exact,GeneralDictionaryGroundCopy218Reinstall.bindings_exact]
  rfl

theorem binder_same (allocated reserved ordinary) (name : Nat) :
    (planFor allocated reserved ordinary).binder name = newPlan.binder name := by
  unfold Plan.binder
  dsimp only
  rw [capture_same]

theorem head_schema_same (allocated reserved ordinary) :
    (planFor allocated reserved ordinary).headSchema = newPlan.headSchema := rfl

theorem variables_same (allocated reserved ordinary) (given : Assignment) :
    GeneralNominalCenteredHeadMatEffects.variables (planFor allocated reserved ordinary) given =
      GeneralNominalCenteredHeadMatEffects.variables newPlan given := by
  funext mode name
  unfold GeneralNominalCenteredHeadMatEffects.variables
  dsimp only
  rw [capture_same,binder_same]

theorem schema_same (allocated reserved ordinary) :
    GeneralNominalCenteredHeadMatPlans.emittedSchema (planFor allocated reserved ordinary) =
      GeneralNominalCenteredHeadMatPlans.emittedSchema newPlan := by
  rw [GeneralDictionaryGroundCopy218Reinstall.schema_exact]
  change GeneralNominalCenteredHeadMatSchemas.generated _ _
    (GeneralNominalCenteredHeadMatSchemas.requests _ registry
      (GeneralNominalDemandMerging.pointSite root).occurrence declaration declaration_checked (packetFor allocated reserved ordinary).bindings) = _
  rw [bindings_exact]
  unfold GeneralNominalCenteredHeadMatSchemas.requests
  simp only [GeneralCanonicalChildOrder.canonicalEmit,GeneralDictionaryGroundCopy218Install.canonical_declaration]
  rfl

theorem outputs_same (allocated reserved ordinary) (given : Assignment) :
    GeneralNominalCenteredHeadMatStepPackets.Outputs (planFor allocated reserved ordinary) given ↔
    GeneralNominalCenteredHeadMatStepPackets.Outputs newPlan given := by
  unfold GeneralNominalCenteredHeadMatStepPackets.Outputs
  rw [schema_same,variables_same]

theorem ordinary_same (allocated reserved ordinary) (given : Assignment) :
    GeneralNominalPacketSupport.Ordinary (packetFor allocated reserved ordinary) given ↔
    GeneralNominalPacketSupport.Ordinary newPacket given := by
  unfold GeneralNominalPacketSupport.Ordinary GeneralNominalPacketSupport.report
  change (GeneralNominalAllocation.Compatible (packetFor allocated reserved ordinary).bindings given ∧
    PresenceNormalForm.All model given (GeneralNominalAllocation.merges _ registry _ declaration _) ∧
    PresenceNormalForm.All model given (selfChecks _ (report (contextFor allocated reserved ordinary) declaration [(6,6)]))) ↔ _
  rw [bindings_exact,GeneralDictionaryGroundCopy218Reinstall.bindings_exact,
    report_exact,GeneralDictionaryGroundCopy218Reinstall.report_exact]
  rfl

theorem projections_same (allocated reserved ordinary) (given : Assignment) :
    ProjectionModels (contextFor allocated reserved ordinary).state
      (report (contextFor allocated reserved ordinary) declaration [(6,6)]) given ↔
    ProjectionModels newPacket.context.state
      (report newPacket.context declaration [(6,6)]) given := by
  rw [report_exact,GeneralDictionaryGroundCopy218Reinstall.report_exact]
  simp [ProjectionModels]
  rfl

theorem child_same (allocated reserved ordinary) (cl : Clause) (valid : cl.Signature roles) :
    (planFor allocated reserved ordinary).childSite cl valid = newPlan.childSite cl valid := by
  unfold Plan.childSite Plan.emittedCenter GeneralNominalFeedbackSites.clauseChild
  simp only [binder_same]
  congr 1
  unfold GeneralNominalFeedbackSites.frame
  rw [bindings_exact,GeneralDictionaryGroundCopy218Reinstall.bindings_exact]
  rfl

theorem child_schema_same (allocated reserved ordinary) (cl : Clause) (valid : cl.Signature roles) :
    GeneralNominalCenteredHeadMatPlans.childSchema (planFor allocated reserved ordinary) cl valid =
    GeneralNominalCenteredHeadMatPlans.childSchema newPlan cl valid := by
  unfold GeneralNominalCenteredHeadMatPlans.childSchema Plan.childRequests
  simp only [Plan.childSite,Plan.emittedCenter,binder_same]

theorem inputs_same (allocated reserved ordinary) (given : Assignment) :
    GeneralNominalCenteredHeadMatStepPackets.Inputs (planFor allocated reserved ordinary) given ↔
    GeneralNominalCenteredHeadMatStepPackets.Inputs newPlan given := by
  unfold GeneralNominalCenteredHeadMatStepPackets.Inputs
  rw [ordinary_same]
  change (_ ∧ ProjectionModels _ (report (contextFor allocated reserved ordinary) declaration [(6,6)]) given ∧ _) ↔ _
  rw [projections_same,schema_same,variables_same,head_schema_same]
  simp only [capture_same,binder_same,Plan.SchemaHolds,child_same,
    child_schema_same,GeneralNominalSharedCaptures.Needed]

open GeneralDictionaryGroundCopy218SaturatedState
open GeneralNominalCenteredHeadOutputs (Frame)
variable {atoms : List (PresenceNormalForm.Atom Nat)}

abbrev currentPlan (atoms) := planFor allocation reservation atoms

theorem children_same (allocated reserved ordinary) :
    (packetFor allocated reserved ordinary).children = newPacket.children := by
  unfold GeneralNominalSaturationState.Packet.children
  change GeneralNominalAllocation.children _ registry _ declaration declaration_checked (packetFor allocated reserved ordinary).bindings = _
  rw [bindings_exact,GeneralDictionaryGroundCopy218Reinstall.bindings_exact]
  rfl

theorem frame_plan {candidate : Plan roles} {key}
    (framed : Frame registry (stage atoms).core root key candidate) : candidate = currentPlan atoms := by
  rcases candidate with ⟨⟨reg,ctx,site,decl,check,bounds⟩,input,inputEq⟩
  have regEq : reg = registry := framed.registry_eq
  have ctxEq : ctx = contextFor allocation reservation atoms := framed.context_eq
  have declEq : decl = declaration := GeneralDictionaryGroundCopy218Install.parent_only framed.visible framed.role_eq
  have raw := framed.raw_recorded
  rw [raw_sites_exact] at raw
  have siteEq : site = GeneralNominalDemandMerging.pointSite root := by
    rcases List.mem_cons.mp raw with yes | raw
    · exact yes
    · rcases List.mem_cons.mp raw with yes | raw
      · have eq := framed.occurrence_eq
        rw [yes] at eq
        have bad := congrArg (fun o : Occurrence roles => o.demand.role) eq
        cases bad
      · have yes := List.mem_singleton.mp raw
        have eq := framed.occurrence_eq
        rw [yes] at eq
        have bad := congrArg (fun o : Occurrence roles => o.demand.role) eq
        cases bad
  have centers := framed.center_recorded
  rw [sites_exact] at centers
  change input ∈ [plan.input,childSite,newChild] at centers
  have inputSame : input = plan.input := by
    rcases List.mem_cons.mp centers with yes | centers
    · exact yes
    · rcases List.mem_cons.mp centers with yes | centers
      · have eq := inputEq.trans framed.occurrence_eq
        rw [yes] at eq
        have bad := congrArg (fun o : Occurrence roles => o.demand.role) eq
        cases bad
      · have yes := List.mem_singleton.mp centers
        have eq := inputEq.trans framed.occurrence_eq
        rw [yes] at eq
        have bad := congrArg (fun o : Occurrence roles => o.demand.role) eq
        cases bad
  subst reg; subst ctx; subst decl; subst site; subst input
  have boundsEq : [(6,6)] = bounds := Option.some.inj framed.located
  subst bounds; rfl

theorem packet_holds (given : Assignment) (held : Models (stage atoms) given) :
    GeneralNominalCenteredHeadMatStepPackets.Holds (currentPlan atoms) given := by
  have prior := held.2.2.2.2.1 newPlan (plans_exact atoms ▸ List.mem_cons_self)
  exact ⟨held.1,(inputs_same allocation reservation atoms given).mpr prior.2.1,
    (outputs_same allocation reservation atoms given).mpr prior.2.2⟩

theorem frame_committed {candidate : Plan roles} {key}
    (framed : Frame registry (stage atoms).core root key candidate) :
    GeneralDictionaryDefaultKernel208.Committed (stage atoms) candidate := by
  cases frame_plan framed
  refine ⟨⟨fun given held => packet_holds given held,?_⟩,?_⟩
  · intro child member
    rw [children_same] at member
    change child ∈ GeneralDictionaryGroundCopy218Reinstall.newChildren at member
    rw [GeneralDictionaryGroundCopy218Reinstall.children_exact] at member
    cases List.mem_singleton.mp member
    rw [edges_exact]
    exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  · intro given held
    exact GeneralDictionaryDefaultSchema208.schema_holds_iff.mpr
      ⟨(packet_holds given held).2.2,class_effects atoms _ _ given⟩

theorem committed (candidate : Effect roles)
    (rootEq : candidate.plan.packet.site.occurrence = root)
    (enabled : GeneralDictionaryDefaultKernel208.Installable registry (stage atoms) candidate) :
    GeneralDictionaryDefaultKernel208.Committed (stage atoms) candidate.plan := by
  have framed : Frame registry (stage atoms).core root candidate.plan.packet.declaration.id candidate.plan := by
    rw [← enabled.registry_eq,← enabled.snapshot_eq,← rootEq]
    exact candidate.frame
  exact frame_committed framed

end Yulang.GeneralDictionaryGroundCopy218SaturatedParent
