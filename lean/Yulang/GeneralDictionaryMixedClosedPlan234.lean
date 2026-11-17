import Yulang.GeneralDictionaryMixedClosedRefresh234
import Yulang.GeneralDictionaryVersionedPoint233
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000
namespace Yulang.GeneralDictionaryMixedClosedPlan234
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229
open GeneralDictionaryMixedClosedSnapshot234
open GeneralNominalCenters GeneralNominalVersionedPlans231
open GeneralDictionaryVersionedNames231 (freshName)
open GeneralDictionaryOptionalInstall229 (actual)
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection

noncomputable abbrev packet : GeneralNominalSaturationState.Packet roles :=
  ⟨registry,extendedContext,GeneralNominalDemandMerging.pointSite root,
    declaration,declaration_checked,[(0,0)]⟩
noncomputable abbrev plan : Plan roles :=
  ⟨packet,rootSite snapshot.seed root,rfl⟩
noncomputable abbrev oldPlan := GeneralDictionaryVersionedPoint233.plan allocated reserved ordinary

theorem query :
    GeneralNominalInspection.queries extendedContext.state interpretation declaration =
      [.nominal 0 [.variables [0],.variables [0]]] := by
  simp [GeneralNominalInspection.queries,Declaration.normalHead,GeneralDeclarationPatterns.normalizeArgs,
    GeneralDeclarationPatterns.normalize,GeneralNominalInspection.translate,interpretation]

theorem report_exact : report extendedContext declaration [(0,0)] =
    { inspected := [(0,0)], checked := [(0,0),(0,0),(2,2),(2,2)],
      captures := [⟨0,(2,2),some (.nominal (.source 0) 0 0)⟩,
        ⟨0,(2,2),some (.nominal (.source 0) 0 1)⟩],
      anchors := [(.nominal (.source 0) 0 0,(2,2)),(.nominal (.source 0) 0 1,(2,2))] } := by
  have sub : inspectMany extendedContext.state [.variables [0],.variables [0]] [(2,2),(2,2)]
      (fun index => some (.nominal (.source 0) 0 index)) 0 =
      { captures := [⟨0,(2,2),some (.nominal (.source 0) 0 0)⟩,
          ⟨0,(2,2),some (.nominal (.source 0) 0 1)⟩],
        checked := [(2,2),(2,2)],
        anchors := [(.nominal (.source 0) 0 0,(2,2)),(.nominal (.source 0) 0 1,(2,2))] } := by
    simp [inspectMany,inspect,Report.append]
  unfold report
  rw [query]
  simp [inspectMany,inspect,typeArguments,Report.append,Report.visit]
  exact ⟨congrArg Report.captures sub,congrArg Report.inspected sub,congrArg Report.checked sub,
    congrArg Report.blocked sub,congrArg Report.conflicts sub,congrArg Report.arity sub,
    congrArg Report.anchors sub,congrArg Report.tests sub⟩

theorem bindings_exact :
    packet.bindings = GeneralDictionaryDefaultMergeRevisionProbe210.twice 0 2 2 := by
  change bindings extendedContext.state
    (report extendedContext declaration [(0,0)]) = _
  rw [report_exact]; rfl

theorem capture_exact :
    (GeneralNominalVersionedFrame231.capture packet).inputs 0 =
      (freshName 0,freshName 1) := by
  change (GeneralNominalVersionedAllocation231.capture extendedContext.state registry root.identity declaration.id packet.bindings).inputs 0 = _
  rw [bindings_exact]
  rfl

theorem binder_exact : GeneralNominalVersionedFrame231.binder plan 0 = actual := by
  rw [GeneralNominalVersionedFrame231.binder_eq]
  unfold Plan.binder
  change (if 0 ∈ declaration.outputNames then _ else if _ then _ else _) = actual
  simp only [show ¬ 0 ∈ declaration.outputNames by decide, ite_false]
  have oldCapture : (GeneralNominalPacketSupport.capture packet).inputs 0 =
      (GeneralDictionaryOptionalInstall229.lo,GeneralDictionaryOptionalInstall229.hi) := by
    unfold GeneralNominalPacketSupport.capture
    rw [bindings_exact]
    rfl
  rw [oldCapture]
  have distinct : GeneralDictionaryOptionalInstall229.lo ≠ GeneralDictionaryOptionalInstall229.hi :=
    Ne.symm (GeneralNominalCenteredAllocation.fresh_namespaces (by decide : (1:Nat) ≠ 0))
  simp only [distinct,ite_false]
  rfl

theorem children_empty : GeneralNominalVersionedFrame231.children packet = [] := by
  unfold GeneralNominalVersionedFrame231.children GeneralDictionaryEmissionPlans.children
    GeneralCanonicalChildOrder.canonicalEmit
  simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_nil]
  rfl

theorem emitted_schema : emittedSchema plan =
    ⟨[⟨4,.actual,GeneralDictionaryOptionalExpression229.expression⟩],false⟩ := by
  unfold emittedSchema emittedRequests
  simp only [GeneralCanonicalChildOrder.canonicalEmit,GeneralCanonicalChildOrder.canonicalDeclaration,
    GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_nil]
  rfl

theorem head_schema : plan.headSchema = GeneralDictionaryOptionalInstall229.plan.headSchema := rfl


end Yulang.GeneralDictionaryMixedClosedPlan234
