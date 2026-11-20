import Yulang.GeneralRebaseRowChildPending287

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 12500000
namespace Yulang.GeneralRebaseRowParentPacket287
open GeneralRebaseRowChildSource287
open GeneralDeclarations GeneralDeclarationPatterns GeneralNominalCenters
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalVersionedPlans231 (emittedSchema childSchema variables)
open GeneralNominalVersionedFrame231 (children binder)
open GeneralNominalCommonBridge (Assignment)

abbrev packet (choice : Bool) : GeneralNominalSaturationState.Packet roles :=
  ⟨registry choice,ctx,GeneralNominalDemandMerging.pointSite root,parentDecl,parent_checked,[(1,1)]⟩
abbrev plan (choice : Bool) : Plan roles := ⟨packet choice,rootSite raw.seed root,rfl⟩
abbrev sign : requirement.Signature roles := parent_checked.signature.2.2.2 _ (List.mem_singleton_self _)
abbrev childId (choice : Bool) :=
  GeneralNominalAllocation.source raw (registry choice) root.identity
    (GeneralNominalAllocation.origin root.identity parentDecl.id 6 requirement.id 0)
abbrev child (choice : Bool) := childAt (childId choice)
abbrev center (choice : Bool) : Site roles := ⟨child choice,fun _ => 0⟩

theorem query : GeneralNominalInspection.queries raw interp parentDecl =
    [.nominal 0 [.variables [0]]] := by
  simp [GeneralNominalInspection.queries,Declaration.normalHead,normalizeArgs,normalize,
    GeneralNominalInspection.translate,constructors]

theorem parent_report (choice : Bool) : GeneralNominalPacketSupport.report (packet choice) =
    GeneralNominalUnaryCaptureFacts.captured raw 1 0 0 (0,0) :=
  GeneralNominalUnaryCaptureFacts.report_exact ctx parentDecl 1 outer rfl 0 (0,0) rfl query

theorem bindings (choice : Bool) : (packet choice).bindings = [(0,(0,0))] := by
  change GeneralNominalRecursiveInspection.bindings raw (GeneralNominalPacketSupport.report (packet choice)) = _
  rw [parent_report]
  rfl

theorem capture (choice : Bool) :
    (GeneralNominalVersionedFrame231.capture (packet choice)).inputs 0 = (0,0) := by
  change (GeneralNominalVersionedAllocation231.capture _ _ _ _ (packet choice).bindings).inputs 0 = _
  rw [bindings]
  rfl

theorem bound_name (choice : Bool) : binder (plan choice) 0 = 0 := by
  unfold binder
  change (if 0 ∈ parentDecl.outputNames then _ else _) = 0
  simp only [show ¬ 0 ∈ parentDecl.outputNames from by decide +kernel]
  rw [capture]
  rfl

theorem sole_child (choice : Bool) : children (packet choice) = [child choice] := by
  unfold children GeneralDictionaryEmissionPlans.children GeneralCanonicalChildOrder.canonicalEmit
  simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,
    List.mergeSort_singleton]
  unfold GeneralNominalVersionedFrame231.frame
  rw [bindings]
  simp [GeneralDeclarationDemands.emitAll,GeneralDeclarationDemands.emit,GeneralDictionaryEmissionPlans.occurrence,
    GeneralDeclarationDemands.childDemand,GeneralDeclarationDemands.inputInterval,requirement,
    GeneralNominalVersionedAllocation231.capture,GeneralNominalAllocation.occurrences,normalize]
  rfl

theorem child_site (choice : Bool) :
    GeneralNominalVersionedFrame231.childSite (plan choice) requirement sign = center choice := by
  unfold GeneralNominalVersionedFrame231.childSite center
  congr 1
  · unfold GeneralNominalVersionedFrame231.clauseChild GeneralNominalVersionedFrame231.capture GeneralNominalVersionedFrame231.frame
    rw [show (plan choice).packet = packet choice from rfl,bindings]
    simp [GeneralDictionaryEmissionPlans.occurrence,GeneralDeclarationDemands.emit,GeneralDeclarationDemands.childDemand,
      GeneralDeclarationDemands.inputInterval,GeneralNominalVersionedAllocation231.capture,
      GeneralNominalAllocation.occurrences,normalize,requirement] <;> rfl
  · funext index
    have zero : index.val = 0 := by have bound := index.isLt; change index.val < 1 at bound; omega
    simpa only [zero,requirement,List.getElem_cons_zero,
      GeneralNominalVersionedFrame231.emittedCenter,normalize] using bound_name choice

abbrev expression : Expr := .nominal 0 [.nominal 0 [.variable 0]]

theorem emitted (choice : Bool) :
    emittedSchema (plan choice) = ⟨[⟨2,.actual,expression⟩,⟨0,.lower,.variable 0⟩,⟨0,.upper,.variable 0⟩],false⟩ := by
  change GeneralNominalCenteredHeadMatSchemas.generated _ _ (GeneralNominalVersionedPlans231.emittedRequests (packet choice)) = _
  unfold GeneralNominalVersionedPlans231.emittedRequests GeneralCanonicalChildOrder.canonicalEmit
  unfold GeneralNominalVersionedFrame231.capture GeneralNominalVersionedFrame231.frame
  rw [bindings]
  simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_singleton]
  rfl

theorem child_schema (choice : Bool) :
    childSchema (plan choice) requirement sign = ⟨[⟨0,.actual,.variable 0⟩],false⟩ := by
  unfold childSchema GeneralNominalVersionedPlans231.childRequests GeneralNominalVersionedFrame231.childSite
  simp only [requirement,List.ofFn_succ,List.ofFn_zero]
  change GeneralNominalCenteredHeadMatSchemas.generated _ _
    [⟨.var 0,binder (plan choice) 0,.actual⟩] = _
  rw [bound_name]
  rfl

theorem variables_same (choice : Bool) (m : Assignment) :
    ∀ mode, variables (plan choice) m mode 0 = (m 0).1 := by
  intro mode
  unfold variables
  change (if 0 ∈ parentDecl.outputNames then _ else _) = _
  simp only [show ¬ 0 ∈ parentDecl.outputNames from by decide +kernel]
  cases mode <;> simp [capture,bound_name]

end Yulang.GeneralRebaseRowParentPacket287
