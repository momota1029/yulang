import Yulang.GeneralWhereVersionRegression317

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 33000
set_option maxHeartbeats 46000000
namespace Yulang.GeneralWhereVersionRootReport317
open GeneralDictionaryJournalRefinement228Source (roles root snapshot)
open GeneralLiveCompoundRegistry316 (registry declaration declaration_checked)
open GeneralWhereVersionSnapshot317 (snap context zero nextDesc)
open GeneralWhereVersionBase317 (two source_old)
open GeneralLiveCompoundPostFrames316 (rootPlan)
open GeneralNominalCenters
open GeneralNominalRecursiveInspection
open GeneralNominalRecursiveCandidates (report arguments)
open GeneralNominalReportErasure (erase interval)
open GeneralNominalCenteredHeadMatPlanData (Same)

noncomputable abbrev packet : GeneralNominalSaturationState.Packet roles :=
  ⟨registry,context,GeneralNominalDemandMerging.pointSite root,declaration,declaration_checked,[(zero,zero)]⟩
noncomputable abbrev plan : Plan roles := ⟨packet,rootSite snapshot.seed root,rfl⟩

theorem location :
    arguments context (GeneralNominalVersionedCandidates231.inputs root) = some [(zero,zero)] := by
  change GeneralCandidateBoundaryParts.locate snap.base [(0,0)] = _
  have atZero := (GeneralDictionaryBinderLocations.sourceSlot_exact snap.base 0 zero).mpr
    (by change GeneralWhereVersionBase317.source zero = 0; rw [source_old]; rfl)
  simp only [GeneralCandidateBoundaryParts.locate,List.mapM_cons,atZero]
  rfl

theorem query : GeneralNominalInspection.queries snap context.interpretation declaration =
    [.nominal 0 [.variables [0],.variables [0]]] := GeneralLiveCompoundCurrentRoot316.query

theorem exact_report : report context declaration [(zero,zero)] =
    { inspected := [(zero,zero)], checked := [(zero,zero),(zero,zero),(two,two),(two,two)],
      captures := [⟨0,(two,two),some (.nominal (.source 0) 0 0)⟩,⟨0,(two,two),some (.nominal (.source 0) 0 1)⟩],
      anchors := [(.nominal (.source 0) 0 0,(two,two)),(.nominal (.source 0) 0 1,(two,two))] } := by
  have atNominal : snap.nominals zero = some nextDesc := rfl
  have arity : typeArguments nextDesc.arguments = some [(two,two),(two,two)] := rfl
  have tag : nextDesc.declaration.name = 0 := rfl
  have src : snap.base.source zero = 0 := by
    change GeneralWhereVersionBase317.source zero = 0
    rw [source_old]; rfl
  have sub : inspectMany snap [.variables [0],.variables [0]] [(two,two),(two,two)]
      (fun index => some (.nominal (.source 0) 0 index)) 0 =
      { captures := [⟨0,(two,two),some (.nominal (.source 0) 0 0)⟩,⟨0,(two,two),some (.nominal (.source 0) 0 1)⟩],
        checked := [(two,two),(two,two)],
        anchors := [(.nominal (.source 0) 0 0,(two,two)),(.nominal (.source 0) 0 1,(two,two))] } := by
    simp [inspectMany,inspect,Report.append]
  unfold report
  rw [query]
  simp [inspectMany,inspect,typeArguments,Report.append,Report.visit,atNominal,tag,src]
  exact ⟨congrArg Report.captures sub,congrArg Report.inspected sub,congrArg Report.checked sub,
    congrArg Report.blocked sub,congrArg Report.conflicts sub,congrArg Report.arity sub,
    congrArg Report.anchors sub,congrArg Report.tests sub⟩

theorem codes :
    erase rootPlan.packet.context.state (GeneralNominalPacketSupport.report rootPlan.packet) =
      erase snap (report context declaration [(zero,zero)]) := by
  let p := GeneralLiveCompoundCurrentRoot316.plan
  let a := GeneralLiveCompoundLeafHead316.packet
  open GeneralNominalVersionedInstallation231 (reserved atoms allocated) in
  change erase (GeneralDictionaryOrdinaryTransport.extendState p.packet.context.state (reserved a) (atoms a) (allocated a))
    (report (GeneralDictionaryOrdinaryTransport.extend p.packet.context (reserved a) (atoms a) (allocated a))
      declaration [((0 : Fin 8),0)]) = _
  rw [GeneralDictionaryOrdinaryTransport.candidate_report_extended,
    GeneralLiveCompoundCurrentRoot316.report_exact,exact_report]
  have s0 : snap.base.source zero = 0 := by
    change GeneralWhereVersionBase317.source zero = 0
    rw [source_old]; rfl
  have s2 : snap.base.source two = 2 := by
    change GeneralWhereVersionBase317.source two = 2
    rw [source_old]; rfl
  simp [erase,interval,s0,s2,GeneralDictionaryOrdinaryTransport.report,
    GeneralDictionaryOrdinaryTransport.capture,GeneralDictionaryOrdinaryTransport.extendState]
  exact ⟨rfl,rfl,rfl⟩

theorem same : Same rootPlan plan :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,codes⟩

end Yulang.GeneralWhereVersionRootReport317
