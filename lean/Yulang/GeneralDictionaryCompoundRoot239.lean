import Yulang.GeneralDictionaryCompoundChild239
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryCompoundRoot239
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryCompoundSource238
open GeneralDictionaryCompoundBase239 GeneralDictionaryCompoundSnapshot239
open GeneralDictionaryCompoundRefresh239
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
noncomputable abbrev packet : GeneralNominalSaturationState.Packet roles :=
  ⟨registry,extendedContext,GeneralNominalDemandMerging.pointSite root,declaration,declaration_checked,[(0,0)]⟩
noncomputable abbrev plan : Plan roles := ⟨packet,rootSite snapshot.seed root,rfl⟩

theorem query : GeneralNominalInspection.queries extendedSnapshot interpretation declaration =
    [.nominal 0 [.variables [0],.variables [0]]] := GeneralDictionaryCompoundChild239.query

theorem report_exact : report extendedContext declaration [(0,0)] =
    { inspected := [(0,0)], checked := [(0,0),(0,0),(2,2),(2,2)],
      captures := [⟨0,(2,2),some (.nominal (.source 0) 0 0)⟩,⟨0,(2,2),some (.nominal (.source 0) 0 1)⟩],
      anchors := [(.nominal (.source 0) 0 0,(2,2)),(.nominal (.source 0) 0 1,(2,2))] } := by
  have sub : inspectMany extendedSnapshot [.variables [0],.variables [0]] [(2,2),(2,2)]
      (fun index => some (.nominal (.source 0) 0 index)) 0 =
      { captures := [⟨0,(2,2),some (.nominal (.source 0) 0 0)⟩,⟨0,(2,2),some (.nominal (.source 0) 0 1)⟩],
        checked := [(2,2),(2,2)],
        anchors := [(.nominal (.source 0) 0 0,(2,2)),(.nominal (.source 0) 0 1,(2,2))] } := by
    simp [inspectMany,inspect,Report.append]
  unfold report
  rw [query]
  simp [inspectMany,inspect,typeArguments,Report.append,Report.visit]
  exact ⟨congrArg Report.captures sub,congrArg Report.inspected sub,congrArg Report.checked sub,
    congrArg Report.blocked sub,congrArg Report.conflicts sub,congrArg Report.arity sub,
    congrArg Report.anchors sub,congrArg Report.tests sub⟩

theorem bindings_exact : packet.bindings = [(0,2,2),(0,2,2)] := by
  change bindings extendedSnapshot (report extendedContext declaration [(0,0)]) = _
  rw [report_exact]
  rfl
end Yulang.GeneralDictionaryCompoundRoot239
