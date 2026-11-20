import Yulang.GeneralObservedLadderReport301
import Yulang.GeneralNominalVersionedChildren232

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 7000000
namespace Yulang.GeneralObservedLadderPlan301
open GeneralObservedLadderSource301 (snapshot nominal_at)
open GeneralObservedLadderInitial301 (context)
open GeneralObservedLadderReport301 (point pos display_query display_report)
open GeneralNominalExamples (registry interpretation displayRoot)
open GeneralDeclarationExamples (roles display display_checked displayChild)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
open GeneralNominalCenters
open GeneralNominalVersionedPlans231
open GeneralNominalVersionedFrame231 (binder capture childSite)
open GeneralNominalRecursiveInspection
open GeneralNominalUnaryCaptureFacts (private_models)
open GeneralSourceDictionaries (Occurrence)

abbrev compiled := GeneralNominalCenteredHeadAllocEncoding.registry registry

abbrev occurrence (i id : Nat) : Occurrence roles :=
  ⟨id,⟨0,fun _ => (i,i),[],by intro _ impossible; cases impossible⟩⟩

abbrev packet (n i id : Nat) (hi : i ≤ n) : GeneralNominalSaturationState.Packet roles :=
  ⟨compiled,context n,GeneralNominalDemandMerging.pointSite (occurrence i id),display,display_checked,
    [point n i (by omega)]⟩

abbrev plan (n i id : Nat) (hi : i ≤ n) : Plan roles :=
  ⟨packet n i id hi,rootSite (snapshot n).seed (occurrence i id),rfl⟩

abbrev origin (i : Nat) : Origin := .nominal (.source i) 0 0

abbrev child (n i id : Nat) (hi : i ≤ n) : Site roles :=
  childSite (plan n i id hi) displayChild (display_checked.signature.2.2.2 _ (by simp))

variable (n i id : Nat) (hi : i ≤ n)

theorem bindings : (packet n i id hi).bindings = [(0,(i+1,i+1))] := by
  change GeneralNominalRecursiveInspection.bindings (snapshot n)
    (GeneralNominalRecursiveCandidates.report (context n) display [point n i (by omega)]) = _
  rw [display_report n i hi]; rfl

theorem captured : (capture (packet n i id hi)).inputs 0 = (i+1,i+1) := by
  unfold capture GeneralNominalVersionedFrame231.frame
  rw [bindings n i id hi]
  rfl

theorem center : binder (plan n i id hi) 0 = i+1 := by
  unfold binder
  change (if 0 ∈ display.outputNames then (capture (packet n i id hi)).outputs 0
    else if ((capture (packet n i id hi)).inputs 0).1 = ((capture (packet n i id hi)).inputs 0).2 then
      ((capture (packet n i id hi)).inputs 0).1 else _) = _
  rw [captured n i id hi]
  simp [GeneralDeclarations.Declaration.outputNames]

theorem head_schema : (plan n i id hi).headSchema =
    ⟨[⟨0,origin i,.actual⟩],[(.source i,.nominal 0 1)],false⟩ := by
  unfold Plan.headSchema
  rw [display_query n]
  simp [GeneralNominalMaterialization.schemas,GeneralNominalMaterialization.schema,
    GeneralNominalMaterialization.Schema.append,rootSite,List.ofFn_succ,origin]

theorem emitted_schema : emittedSchema (plan n i id hi) =
    ⟨[⟨i+1,.lower,.variable 0⟩,⟨i+1,.upper,.variable 0⟩],false⟩ := by
  change GeneralNominalCenteredHeadMatSchemas.generated _ _ (emittedRequests (packet n i id hi)) = _
  unfold emittedRequests GeneralCanonicalChildOrder.canonicalEmit
  unfold GeneralNominalVersionedFrame231.capture GeneralNominalVersionedFrame231.frame
  rw [bindings n i id hi]
  simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,
    List.mergeSort_singleton]
  rfl

theorem emitted_sites : GeneralNominalVersionedChildren232.emitted (plan n i id hi) = [child n i id hi] := by
  have length : (GeneralNominalVersionedChildren232.emitted (plan n i id hi)).length = 1 :=
    GeneralNominalVersionedChildren232.emitted_length _
  have seen : child n i id hi ∈ GeneralNominalVersionedChildren232.emitted (plan n i id hi) := by
    unfold GeneralNominalVersionedChildren232.emitted
    have member : displayChild ∈ GeneralCanonicalChildOrder.canonicalRequirements (plan n i id hi).packet.declaration.requirements :=
      (GeneralCanonicalChildOrder.canonicalRequirements_perm _).mem_iff.mp (List.mem_singleton_self _)
    exact List.mem_map.mpr ⟨⟨_,member⟩,List.mem_attach _ _,rfl⟩
  obtain ⟨one,view⟩ := List.length_eq_one_iff.mp length
  rw [view] at seen ⊢
  cases List.mem_singleton.mp seen
  rfl

theorem child_args : ∀ k, (child n i id hi).occurrence.demand.arguments k = (i+1,i+1) := by
  intro k
  have kz : k.val = 0 := by have h := k.isLt; change k.val < 1 at h; omega
  unfold child GeneralNominalVersionedFrame231.childSite
  change (GeneralDeclarationDemands.childDemand display displayChild (display_checked.signature.2.2.2 _ (by simp))
    (capture (packet n i id hi)) _).arguments k = _
  simpa [GeneralDeclarationDemands.childDemand,GeneralDeclarationDemands.inputInterval,displayChild,kz,
    GeneralDeclarationPatterns.normalize] using captured n i id hi

theorem child_center : ∀ k, (child n i id hi).center k = i+1 := by
  intro k
  have kz : k.val = 0 := by have h := k.isLt; change k.val < 1 at h; omega
  unfold child
  simpa only [kz,displayChild,List.getElem_cons_zero,
    GeneralNominalVersionedFrame231.childSite,GeneralNominalVersionedFrame231.emittedCenter,
    GeneralDeclarationPatterns.normalize] using center n i id hi

theorem child_schema : childSchema (plan n i id hi) displayChild
    (display_checked.signature.2.2.2 _ (by simp)) = ⟨[⟨i+1,.actual,.variable 0⟩],false⟩ := by
  unfold childSchema childRequests
  simp only [displayChild,List.ofFn_succ,List.ofFn_zero]
  change GeneralNominalCenteredHeadMatSchemas.generated _ _ [⟨.var 0,(child n i id hi).center _,.actual⟩] = _
  rw [child_center n i id hi]
  rfl

theorem var_actual (m : Assignment) : variables (plan n i id hi) m .actual 0 = (m (i+1)).1 := by
  unfold variables
  rw [center n i id hi]
  rfl

theorem var_bounds (m : Assignment) :
    variables (plan n i id hi) m .lower 0 = (m (i+1)).1 ∧
      variables (plan n i id hi) m .upper 0 = (m (i+1)).1 := by
  unfold variables
  rw [captured n i id hi]
  exact ⟨rfl,rfl⟩

end Yulang.GeneralObservedLadderPlan301
