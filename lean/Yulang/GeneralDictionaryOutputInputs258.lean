import Yulang.GeneralDictionaryOutputPremise258
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryOutputInputs258
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries GeneralNominalCenters
open GeneralDictionaryOutputDepth252
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRecursiveInspection GeneralNominalRecursiveCandidates
open CommonNominalFullCarrier
theorem projection (assignment : Assignment) : ProjectionModels snapshot (GeneralNominalPacketSupport.report packet) assignment := by
 change ProjectionModels snapshot (report context declaration [(2,2)]) assignment
 rw [report_exact]
 refine ⟨(by intro _ h; cases h),(by intro _ h; cases h),?_,?_⟩
 · intro first one last two _ ref located
   cases List.mem_singleton.mp one
   cases located
 · intro first one last two _ a b located
   cases List.mem_singleton.mp one
   cases located

theorem ordinary (assignment : Assignment) : GeneralNominalVersionedPlans231.Ordinary packet assignment := by
 refine ⟨?_,?_,?_⟩
 · rw [bindings_exact]
   intro first one last two _
   cases List.mem_singleton.mp one
   cases List.mem_singleton.mp two
   exact subtype_refl _
 · rw [bindings_exact]
   change PresenceNormalForm.All CommonNominalFullCarrier.model assignment []
   exact PresenceNormalForm.all_nil _ _
 · change PresenceNormalForm.All CommonNominalFullCarrier.model assignment (selfChecks snapshot (report context declaration [(2,2)]))
   rw [report_exact]
   change PresenceNormalForm.All CommonNominalFullCarrier.model assignment [.tyLe (.var 2) (.var 2),.tyLe (.var 2) (.var 2)]
   intro atom member
   rcases List.mem_cons.mp member with rfl | member
   · exact subtype_refl _
   · cases List.mem_singleton.mp member
     exact subtype_refl _

theorem head_holds (assignment : Assignment) : GeneralNominalVersionedPlans231.SchemaHolds plan plan.headSchema assignment := by
 have schema : plan.headSchema = {variables := [⟨0,.source 2,.actual⟩]} := by
   simp [Plan.headSchema,GeneralNominalInspection.queries,Declaration.normalHead,normalizeArgs,normalize,GeneralNominalInspection.translate,GeneralNominalMaterialization.schemas,GeneralNominalMaterialization.schema,GeneralNominalMaterialization.Schema.append]
   rfl
 rw [schema]
 constructor
 · intro test member; cases member
 · intro entry member
   change entry ∈ [⟨0,.source 2,.actual⟩] at member
   cases List.mem_singleton.mp member
   change GeneralNominalOriginTerms.Same assignment (.source 2) (.source (GeneralNominalVersionedFrame231.binder plan 0))
   rw [binder_exact]
   exact ⟨⟨_,.source 2⟩,⟨_,.source 2⟩,fun x y a b => by cases a; cases b; exact ⟨subtype_refl _,subtype_refl _⟩⟩

theorem inputs (assignment : Assignment) : GeneralNominalVersionedPlans231.Inputs plan assignment := by
 refine ⟨ordinary assignment,projection assignment,?_,?_,head_holds assignment,?_,?_⟩
 · intro index; exact ⟨subtype_refl _,subtype_refl _⟩
 · intro name needed
   have equal : name = 0 := by
     rcases needed with named | ⟨clause,member,_⟩
     · simpa [Declaration.inputNames,variablesArgs,normalizeArgs,normalize,Pattern.variables] using named
     · cases member
   subst name
   rw [binder_exact]
   unfold GeneralNominalVersionedFrame231.capture GeneralNominalVersionedFrame231.frame GeneralNominalVersionedAllocation231.capture
   rw [bindings_exact]
   exact ⟨subtype_refl _,subtype_refl _⟩
 · intro equation member nonactual
   rw [emitted_exact] at member
   cases List.mem_singleton.mp member
   exact False.elim (nonactual rfl)
 · intro clause member; cases member

theorem packet_exact (assignment : Assignment) :
 GeneralNominalVersionedPlans231.Holds plan assignment ↔
 GeneralNominalState.Models snapshot assignment ∧ GeneralNominalVersionedPlans231.Outputs plan assignment := by
 constructor
 · intro valid; exact ⟨valid.1,valid.2.2⟩
 · rintro ⟨raw,outputs⟩; exact ⟨raw,inputs assignment,outputs⟩
end Yulang.GeneralDictionaryOutputInputs258
