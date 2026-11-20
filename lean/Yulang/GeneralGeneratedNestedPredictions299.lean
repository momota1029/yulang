import Yulang.GeneralGeneratedNestedInitial299

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 26500
set_option maxHeartbeats 9500000
namespace Yulang.GeneralGeneratedNestedPredictions299
open GeneralGeneratedNestedSource299
open GeneralDeclarationExamples (roles display display_checked)
open GeneralNominalExamples (registry intDisplay int_display_checked interpretation)
open GeneralNominalSaturationState (Packet)
open GeneralNominalRecursiveInspection
open GeneralNominalRecursiveCandidates (report)
open GeneralNominalUnaryCaptureFacts (captured report_exact)
open GeneralNominalVersionedFrame231 (children)
open GeneralNominalDemandMerging (pointSite)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedCandidates231 (inputs)

abbrev compiled := GeneralNominalCenteredHeadAllocEncoding.registry registry

theorem query : GeneralNominalInspection.queries snapshot interpretation display =
    [.nominal 0 [.variables [0]]] := by
  simp [GeneralNominalInspection.queries,GeneralDeclarations.Declaration.normalHead,
    GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
    GeneralNominalInspection.translate,interpretation]

theorem root_report : report context display [(0,0)] = captured snapshot 0 0 0 (1,1) :=
  report_exact context display 0 (listDescriptor 1) rfl 0 (1,1) rfl query

theorem middle_report : report context display [(1,1)] = captured snapshot 1 0 0 (2,2) :=
  report_exact context display 1 (listDescriptor 2) rfl 0 (2,2) rfl query

theorem terminal_report : report context intDisplay [(2,2)] =
    { inspected := [(2,2)], checked := [(2,2),(2,2)] } := by
  have test : GeneralNominalInspection.queries snapshot interpretation intDisplay = [.scalar .int] := by
    simp [GeneralNominalInspection.queries,GeneralDeclarations.Declaration.normalHead,
      GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
      GeneralNominalInspection.translate,interpretation]
  unfold report
  rw [show GeneralNominalInspection.queries context.state context.interpretation intDisplay = _
    from test]
  simp [inspectMany,inspect,Report.visit,Report.append]

abbrev parentPacket : Packet roles :=
  ⟨compiled,context,pointSite (inputs root),display,display_checked,[(0,0)]⟩

abbrev middle : Occurrence roles := (children parentPacket).headD root

abbrev middlePacket : Packet roles :=
  ⟨compiled,context,pointSite middle,display,display_checked,[(1,1)]⟩

abbrev terminal : Occurrence roles := (children middlePacket).headD middle

abbrev terminalPacket : Packet roles :=
  ⟨compiled,context,pointSite terminal,intDisplay,int_display_checked,[(2,2)]⟩

theorem one_child (packet : Packet roles) (fallback : Occurrence roles)
    (one : (children packet).length = 1) :
    children packet = [(children packet).headD fallback] := by
  obtain ⟨d,view⟩ := List.length_eq_one_iff.mp one
  simp [view]

theorem parent_children : children parentPacket = [middle] := by
  apply one_child
  have len := congrArg List.length (GeneralNominalVersionedChildren232.emitted_occurrences
    (⟨parentPacket,GeneralNominalCenters.rootSite snapshot.seed root,rfl⟩))
  simpa [GeneralNominalVersionedChildren232.emitted_length] using len.symm

theorem middle_children : children middlePacket = [terminal] := by
  apply one_child
  have len := congrArg List.length (GeneralNominalVersionedChildren232.emitted_occurrences
    (⟨middlePacket,GeneralNominalCenters.rootSite snapshot.seed middle,rfl⟩))
  simpa [GeneralNominalVersionedChildren232.emitted_length] using len.symm

theorem terminal_children : children terminalPacket = [] := by
  apply List.length_eq_zero_iff.mp
  have len := congrArg List.length (GeneralNominalVersionedChildren232.emitted_occurrences
    (⟨terminalPacket,GeneralNominalCenters.rootSite snapshot.seed terminal,rfl⟩))
  simpa [GeneralNominalVersionedChildren232.emitted_length] using len.symm

theorem middle_bounds : middle.demand.arguments ⟨0,by decide +kernel⟩ = (1,1) := by
  decide +kernel

theorem terminal_bounds : terminal.demand.arguments ⟨0,by decide +kernel⟩ = (2,2) := by
  decide +kernel

theorem different_occurrences : root.identity ≠ middle.identity ∧ middle.identity ≠ terminal.identity := by
  decide +kernel

end Yulang.GeneralGeneratedNestedPredictions299
