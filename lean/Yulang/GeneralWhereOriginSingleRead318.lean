import Yulang.GeneralWhereOriginSingleSource318

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000
set_option maxHeartbeats 9000000
namespace Yulang.GeneralWhereOriginSingleRead318
open GeneralWhereOriginSingleSource318
open GeneralDeclarations GeneralDeclarationPatterns
open GeneralDictionaryJournalRefinement228Source (roles root snapshot state context interpretation)
open GeneralLiveCompoundRegistry316 (otherChild)
open GeneralLiveCompoundUpperSnapshot316 (snap)
open GeneralNominalRecursiveCandidates (report)
open GeneralNominalRecursiveInspection
open GeneralWhereVersionCase317 (expr)
open GeneralVersionedEndpointAddress315 (atCell footprint fields)
open GeneralNominalVersionedExpressionFrame236 (variableSource)
open GeneralWhereOriginDelta318 (Cell)

abbrev firstOrigin : Origin := .nominal (.source 0) 0 0
abbrev secondOrigin : Origin := .nominal (.source 0) 0 1

theorem old_query : GeneralNominalInspection.queries snapshot interpretation declaration =
    [.nominal 0 [.variables [0],.variables [1]]] := by
  simp [GeneralNominalInspection.queries,Declaration.normalHead,normalizeArgs,normalize,
    GeneralNominalInspection.translate,interpretation]

theorem new_query : GeneralNominalInspection.queries snap interpretation declaration =
    [.nominal 0 [.variables [0],.variables [1]]] := old_query

theorem old_report : report context declaration [(0,0)] =
    { inspected := [(0,0)], checked := [(0,0),(0,0),(4,2),(4,2)],
      captures := [⟨0,(4,2),some firstOrigin⟩,⟨1,(4,2),some secondOrigin⟩],
      anchors := [(firstOrigin,(4,2)),(secondOrigin,(4,2))] } := by
  unfold report
  rw [old_query]
  simp [inspectMany,inspect,Report.visit,Report.append,typeArguments,state]
  rw [inspectMany.eq_2,inspectMany.eq_2,inspectMany.eq_1]
  simp only [inspect.eq_1,Report.append]
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem new_report : report GeneralLiveCompoundUpperSnapshot316.context declaration [(0,0)] =
    { inspected := [(0,0)], checked := [(0,0),(0,0),(2,2),(2,2)],
      captures := [⟨0,(2,2),some firstOrigin⟩,⟨1,(2,2),some secondOrigin⟩],
      anchors := [(firstOrigin,(2,2)),(secondOrigin,(2,2))] } := by
  have sub : inspectMany snap [.variables [0],.variables [1]] [(2,2),(2,2)]
      (fun i => some (.nominal (.source 0) 0 i)) 0 =
      { captures := [⟨0,(2,2),some firstOrigin⟩,⟨1,(2,2),some secondOrigin⟩],
        checked := [(2,2),(2,2)],anchors := [(firstOrigin,(2,2)),(secondOrigin,(2,2))] } := by
    simp [inspectMany,inspect,Report.append,firstOrigin,secondOrigin]
  unfold report
  rw [new_query]
  simp [inspectMany,inspect,typeArguments,Report.append,Report.visit]
  exact ⟨congrArg Report.captures sub,congrArg Report.inspected sub,congrArg Report.checked sub,
    congrArg Report.blocked sub,congrArg Report.conflicts sub,congrArg Report.arity sub,
    congrArg Report.anchors sub,congrArg Report.tests sub⟩

theorem old_bindings : older.bindings = [(0,4,2),(1,4,2)] := by
  change bindings snapshot (report context declaration [(0,0)]) = _
  rw [old_report]
  rfl

theorem new_bindings : newer.bindings = [(0,2,2),(1,2,2)] := by
  change bindings snap (report GeneralLiveCompoundUpperSnapshot316.context declaration [(0,0)]) = _
  rw [new_report]; rfl

theorem old_reads : variableSource oldPlan .lower 0 = 4 ∧ variableSource oldPlan .upper 0 = 2 := by
  unfold variableSource
  have no : ¬ (0:Nat) ∈ declaration.outputNames := by decide +kernel
  simp only [ite_eq_right no]
  change ((GeneralNominalVersionedAllocation231.capture _ _ _ _ older.bindings).inputs 0).1 = 4 ∧
    ((GeneralNominalVersionedAllocation231.capture _ _ _ _ older.bindings).inputs 0).2 = 2
  rw [old_bindings]
  exact ⟨rfl,rfl⟩

theorem new_reads : variableSource newPlan .lower 0 = 2 ∧ variableSource newPlan .upper 0 = 2 := by
  unfold variableSource
  have no : ¬ (0:Nat) ∈ declaration.outputNames := by decide +kernel
  simp only [ite_eq_right no]
  change ((GeneralNominalVersionedAllocation231.capture _ _ _ _ newer.bindings).inputs 0).1 = 2 ∧
    ((GeneralNominalVersionedAllocation231.capture _ _ _ _ newer.bindings).inputs 0).2 = 2
  rw [new_bindings]
  exact ⟨rfl,rfl⟩

end Yulang.GeneralWhereOriginSingleRead318
