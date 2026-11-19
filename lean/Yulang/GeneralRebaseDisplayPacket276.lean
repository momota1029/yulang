import Yulang.GeneralNominalMixedNonleaf198
import Yulang.GeneralRebaseNonleafRetarget276

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 25000
set_option maxHeartbeats 8500000
namespace Yulang.GeneralRebaseDisplayPacket276
open GeneralNominalNonleafPlan193 (plan packet declaration bindings binder_zero first_child centerSite equations branch head_schema)
open GeneralNominalExamples (registry context state displayRoot displayChild model state_models)
open GeneralDeclarationExamples (roles display_checked)
open GeneralNominalCenters (Plan)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedPlans231
open CommonNominalFullCarrier

theorem children : GeneralNominalVersionedFrame231.children packet = [displayChild] := by
 unfold GeneralNominalVersionedFrame231.children GeneralDictionaryEmissionPlans.children
   GeneralCanonicalChildOrder.canonicalEmit
 simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,
   List.mergeSort_singleton]
 unfold GeneralNominalVersionedFrame231.frame
 rw [bindings]
 simp [GeneralDeclarationDemands.emitAll,GeneralDeclarationDemands.emit,GeneralDictionaryEmissionPlans.occurrence,
   GeneralDeclarationDemands.childDemand,GeneralDeclarationDemands.inputInterval,GeneralDeclarationExamples.displayChild,
   GeneralNominalVersionedAllocation231.capture,GeneralNominalAllocation.occurrences,GeneralDeclarationPatterns.normalize]
 rfl

theorem center : GeneralNominalVersionedFrame231.binder plan 0 = 1 :=
 (GeneralNominalVersionedFrame231.binder_eq plan 0).trans binder_zero

theorem capture : (GeneralNominalVersionedFrame231.capture packet).inputs 0 = (1,1) := by
 change (GeneralNominalVersionedAllocation231.capture _ _ _ _ packet.bindings).inputs 0 = _
 rw [bindings]
 rfl

theorem child_site :
 GeneralNominalVersionedFrame231.childSite plan GeneralDeclarationExamples.displayChild
  (display_checked.signature.2.2.2 _ (by simp)) = centerSite := by
 unfold GeneralNominalVersionedFrame231.childSite centerSite
 congr 1
 · unfold GeneralNominalVersionedFrame231.clauseChild GeneralNominalVersionedFrame231.capture GeneralNominalVersionedFrame231.frame
   rw [show plan.packet = packet from rfl,bindings]
   simp [GeneralDictionaryEmissionPlans.occurrence,GeneralDeclarationDemands.emit,GeneralDeclarationDemands.childDemand,
     GeneralDeclarationDemands.inputInterval,GeneralNominalVersionedAllocation231.capture,GeneralNominalAllocation.occurrences,
     GeneralDeclarationPatterns.normalize,displayChild,GeneralDeclarationExamples.displayChild,packet,displayRoot,
     GeneralNominalDemandMerging.pointSite]
 · funext i
   have zero : i.val = 0 := by have bound := i.isLt; change i.val < 1 at bound; omega
   simpa only [zero,GeneralDeclarationExamples.displayChild,List.getElem_cons_zero,GeneralNominalVersionedFrame231.emittedCenter,GeneralDeclarationPatterns.normalize] using center

theorem emitted :
 emittedSchema plan = ⟨[⟨1,.lower,.variable 0⟩,⟨1,.upper,.variable 0⟩],false⟩ := by
 change GeneralNominalCenteredHeadMatSchemas.generated _ _ (emittedRequests packet) = _
 unfold emittedRequests GeneralCanonicalChildOrder.canonicalEmit
 unfold GeneralNominalVersionedFrame231.capture GeneralNominalVersionedFrame231.frame
 rw [bindings]
 simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,
   List.mergeSort_singleton]
 rfl

theorem child_schema :
 childSchema plan GeneralDeclarationExamples.displayChild (display_checked.signature.2.2.2 _ (by simp)) =
 ⟨[⟨1,.actual,.variable 0⟩],false⟩ := by
 unfold childSchema childRequests GeneralNominalVersionedFrame231.childSite
 simp only [GeneralDeclarationExamples.displayChild,List.ofFn_succ,List.ofFn_zero]
 change GeneralNominalCenteredHeadMatSchemas.generated _ _
   [⟨.var 0,GeneralNominalVersionedFrame231.binder plan 0,.actual⟩] = _
 rw [center]
 rfl

theorem real_variable (m : Assignment) : variables plan m .actual 0 = (m 1).1 := by
 rw [actual_variables]
 unfold GeneralNominalCenteredHeadMatEffects.variables
 rw [binder_zero]
 by_cases h : 0 ∈ plan.packet.declaration.outputNames <;> simp only [h,ite_true,ite_false]

theorem bound_values (m : Assignment) :
 variables plan m .lower 0 = (m 1).1 ∧ variables plan m .upper 0 = (m 1).1 := by
 unfold variables
 change (if 0 ∈ declaration.outputNames then _ else (m ((GeneralNominalVersionedFrame231.capture packet).inputs 0).1).1) = _ ∧
   (if 0 ∈ declaration.outputNames then _ else (m ((GeneralNominalVersionedFrame231.capture packet).inputs 0).2).1) = _
 rw [capture]
 exact ⟨rfl,rfl⟩

theorem ordinary_exact (m : Assignment) (valid : GeneralNominalState.Models (state true) m) :
 Ordinary packet m := by
 have old := (GeneralNominalPacketSupport.private_exact packet m).mp (branch m valid).1
 refine ⟨old.2.1,?_,old.2.2.2⟩
 unfold GeneralNominalVersionedAllocation231.merges
 rw [bindings]
 intro atom present
 cases present

theorem holds (m : Assignment) (valid : GeneralNominalState.Models (state true) m) : Holds plan m := by
 have eqs := equations m valid
 refine ⟨valid,⟨ordinary_exact m valid,(branch m valid).2.1,eqs.1,?_,?_,?_,?_⟩,?_⟩
 · intro name used
   have zero : name = 0 := by
     rcases used with head | ⟨clause,member,used⟩
     · simpa [packet,declaration,GeneralDeclarations.Declaration.inputNames,GeneralDeclarationPatterns.variablesArgs,
         GeneralDeclarationPatterns.Pattern.variables,GeneralDeclarationPatterns.normalizeArgs,
         GeneralDeclarationPatterns.normalize] using head
     · cases List.mem_singleton.mp member
       simpa [GeneralDeclarationPatterns.variablesArgs,GeneralDeclarationPatterns.Pattern.variables,
           GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
           GeneralDeclarationExamples.displayChild] using used
   subst name
   change GeneralNominalCaptureMerges.Fits m ((GeneralNominalVersionedFrame231.capture packet).inputs 0)
     (m (GeneralNominalVersionedFrame231.binder plan 0)).1
   rw [capture,center]
   exact ⟨subtype_refl _,subtype_refl _⟩
 · have oldHead := eqs.2.2.1
   rw [head_schema] at oldHead
   rw [head_schema]
   refine ⟨oldHead.1,?_⟩
   intro entry member
   cases List.mem_singleton.mp member
   simp only [ite_true,center]
   have original := oldHead.2 _ (List.mem_singleton_self _)
   simpa only [ite_true,binder_zero] using original
 · rw [emitted]
   intro entry member _
   rcases List.mem_cons.mp member with rfl|rest
   · change Equivalent (m 1).1 (variables plan m .lower 0)
     rw [(bound_values m).1]
     exact ⟨subtype_refl _,subtype_refl _⟩
   · cases List.mem_singleton.mp rest
     change Equivalent (m 1).1 (variables plan m .upper 0)
     rw [(bound_values m).2]
     exact ⟨subtype_refl _,subtype_refl _⟩
 · intro clause member signature
   change clause ∈ declaration.requirements at member
   cases List.mem_singleton.mp member
   rw [child_site,child_schema]
   refine ⟨?_,?_⟩
   · intro i
     exact ⟨subtype_refl _,subtype_refl _⟩
   · intro entry member
     cases List.mem_singleton.mp member
     change Equivalent (m 1).1 (variables plan m .actual 0)
     rw [real_variable]
     exact ⟨subtype_refl _,subtype_refl _⟩
 · unfold Outputs
   rw [emitted]
   intro entry member
   rcases List.mem_cons.mp member with rfl|rest
   · change Equivalent (m 1).1 (variables plan m .lower 0)
     rw [(bound_values m).1]
     exact ⟨subtype_refl _,subtype_refl _⟩
   · cases List.mem_singleton.mp rest
     change Equivalent (m 1).1 (variables plan m .upper 0)
     rw [(bound_values m).2]
     exact ⟨subtype_refl _,subtype_refl _⟩

end Yulang.GeneralRebaseDisplayPacket276
