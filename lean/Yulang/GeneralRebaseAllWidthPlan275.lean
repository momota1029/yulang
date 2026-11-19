import Yulang.GeneralRebaseAllWidthRealized275

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 21000
set_option maxHeartbeats 6700000
namespace Yulang.GeneralRebaseAllWidthPlan275

open GeneralDictionaryJournalRefinement228Source (roles root snapshot interpretation)
open GeneralDictionaryOptionalInitial229 (registry declaration declaration_checked)
open GeneralDictionaryVersionedSecondInstall233 (installed)
open GeneralRebaseAllWidthRealized275 (successor)
open GeneralRebaseAllWidthCertificate275 (context)
open GeneralDeclarations GeneralNominalCenters
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedPlans231
local notation "s0" => (0 : Fin 8)
local notation "s2" => (2 : Fin 8)

noncomputable abbrev packet : GeneralNominalSaturationState.Packet roles :=
 ⟨registry,context,GeneralNominalDemandMerging.pointSite root,declaration,declaration_checked,[(s0,s0)]⟩

noncomputable abbrev plan : Plan roles := ⟨packet,rootSite snapshot.seed root,rfl⟩

noncomputable abbrev retained := GeneralDictionaryVersionedSecondInstall233.plan

theorem located :
 arguments context (GeneralNominalVersionedCandidates231.inputs root) = some packet.bounds := by
 rfl

theorem query : GeneralNominalInspection.queries context.state interpretation declaration =
 [.nominal 0 [.variables [0],.variables [0]]] := by
 have constructor0 : context.state.constructors 0 = some ⟨[.type,.type],0⟩ := rfl
 simp [GeneralNominalInspection.queries,Declaration.normalHead,GeneralDeclarationPatterns.normalizeArgs,
   GeneralDeclarationPatterns.normalize,GeneralNominalInspection.translate,interpretation,constructor0]

theorem report_exact : report context declaration [(s0,s0)] =
    { inspected := [(s0,s0)], checked := [(s0,s0),(s0,s0),(s2,s2),(s2,s2)],
      captures := [⟨0,(s2,s2),some (.nominal (.source 0) 0 0)⟩,
        ⟨0,(s2,s2),some (.nominal (.source 0) 0 1)⟩],
      anchors := [(.nominal (.source 0) 0 0,(s2,s2)),(.nominal (.source 0) 0 1,(s2,s2))] } := by
 have sub : inspectMany context.state [.variables [0],.variables [0]] [(s2,s2),(s2,s2)]
      (fun index => some (.nominal (.source 0) 0 index)) 0 =
      { captures := [⟨0,(s2,s2),some (.nominal (.source 0) 0 0)⟩,
          ⟨0,(s2,s2),some (.nominal (.source 0) 0 1)⟩],
        checked := [(s2,s2),(s2,s2)],
        anchors := [(.nominal (.source 0) 0 0,(s2,s2)),(.nominal (.source 0) 0 1,(s2,s2))] } := by
    simp [inspectMany,inspect,Report.append]
 unfold report
 rw [show GeneralNominalInspection.queries context.state context.interpretation declaration = _ from query]
 simp [inspectMany,inspect,typeArguments,Report.append,Report.visit]
 exact ⟨congrArg Report.captures sub,congrArg Report.inspected sub,congrArg Report.checked sub,
    congrArg Report.blocked sub,congrArg Report.conflicts sub,congrArg Report.arity sub,
    congrArg Report.anchors sub,congrArg Report.tests sub⟩

theorem bindings_exact : packet.bindings = GeneralDictionaryVersionedNames231.newBindings := by
 change bindings context.state (report context declaration [(s0,s0)]) = _
 rw [report_exact]
 rfl

theorem children_empty : GeneralNominalVersionedFrame231.children plan.packet = [] := by
 unfold GeneralNominalVersionedFrame231.children GeneralDictionaryEmissionPlans.children
   GeneralCanonicalChildOrder.canonicalEmit
 simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_nil]
 rfl

theorem unchanged_schema : emittedSchema plan = emittedSchema retained := by
 unfold emittedSchema emittedRequests
 simp only [GeneralCanonicalChildOrder.canonicalEmit,GeneralCanonicalChildOrder.canonicalDeclaration,
   GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_nil]
 rfl

theorem unchanged_head : plan.headSchema = retained.headSchema := by rfl

theorem unchanged_capture : GeneralNominalVersionedFrame231.capture plan.packet =
  GeneralNominalVersionedFrame231.capture retained.packet := by
 change GeneralNominalVersionedAllocation231.capture context.state registry root.identity declaration.id packet.bindings =
   GeneralNominalVersionedAllocation231.capture _ registry root.identity declaration.id retained.packet.bindings
 rw [bindings_exact,GeneralDictionaryVersionedPoint233.bindings_exact]
 rfl

theorem unchanged_binder (name : Nat) : GeneralNominalVersionedFrame231.binder plan name =
 GeneralNominalVersionedFrame231.binder retained name := by
 unfold GeneralNominalVersionedFrame231.binder
 rw [unchanged_capture]
 rfl

theorem unchanged_variables (m : Assignment) (mode) (name : Nat) :
 variables plan m mode name = variables retained m mode name := by
 unfold variables
 rw [unchanged_binder,unchanged_capture]

end Yulang.GeneralRebaseAllWidthPlan275
