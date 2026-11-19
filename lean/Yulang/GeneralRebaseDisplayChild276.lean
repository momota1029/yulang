import Yulang.GeneralRebaseDisplayFrame276

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 25000
set_option maxHeartbeats 8500000
namespace Yulang.GeneralRebaseDisplayChild276
open GeneralNominalExamples (registry state displayRoot displayChild intDisplay int_display_checked model)
open GeneralDeclarationExamples (roles)
open GeneralNominalNonleafPlan193 (centerSite)
open GeneralRebaseDisplayFrame276 (after emitted_site no_new_request)
open GeneralNominalCenters
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedPlans231
open GeneralNominalRecursiveInspection
open CommonNominalFullCarrier

noncomputable abbrev context := after.core.erased.current.context
noncomputable abbrev packet : GeneralNominalSaturationState.Packet roles :=
 ⟨registry,context,centerSite.observed,intDisplay,int_display_checked,[((1 : Fin 2),(1 : Fin 2))]⟩
noncomputable abbrev plan : Plan roles := ⟨packet,centerSite,rfl⟩

theorem query : GeneralNominalInspection.queries context.state context.interpretation intDisplay = [.scalar .int] := by
 change GeneralNominalInspection.queries (state true) GeneralNominalExamples.interpretation intDisplay = _
 simp [GeneralNominalInspection.queries,GeneralDeclarations.Declaration.normalHead,
   GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
   GeneralNominalInspection.translate,GeneralNominalExamples.interpretation]

theorem report_exact : GeneralNominalPacketSupport.report packet =
 { inspected := [((1 : Fin 2),(1 : Fin 2))], checked := [((1 : Fin 2),(1 : Fin 2)),((1 : Fin 2),(1 : Fin 2))] } := by
 unfold GeneralNominalPacketSupport.report GeneralNominalRecursiveCandidates.report
 have same : GeneralNominalInspection.queries packet.context.state packet.context.interpretation packet.declaration = _ := query
 rw [same]
 have no : context.state.nominals (1 : Fin 2) = none := rfl
 have scalar : context.state.view.heads (1 : Fin 2) = .scalar .int := rfl
 simp [inspectMany,inspect,Report.visit,Report.append,no,scalar]

theorem bindings_empty : packet.bindings = [] := by
 change bindings context.state (GeneralNominalPacketSupport.report packet) = []
 rw [report_exact]
 rfl

theorem no_children : GeneralNominalVersionedFrame231.children packet = [] := by
 unfold GeneralNominalVersionedFrame231.children GeneralDictionaryEmissionPlans.children
 rw [GeneralRebaseRetarget275.no_emission _ _ _ _ _ (show intDisplay.requirements = [] from rfl)]
 rfl

theorem emitted_empty : emittedSchema plan = ⟨[],false⟩ := by
 unfold emittedSchema emittedRequests
 rw [GeneralRebaseRetarget275.no_emission _ _ _ _ _ (show intDisplay.requirements = [] from rfl)]
 rfl

theorem ordinary (m : Assignment) : Ordinary packet m := by
 refine ⟨?_,?_,?_⟩
 · rw [bindings_empty]
   exact fun _ member => False.elim (List.not_mem_nil member)
 · intro a member
   cases member
 · rw [report_exact]
   simp [selfChecks,PresenceNormalForm.All]
   exact subtype_refl _

theorem head_schema : plan.headSchema = ⟨[],[(.source 1,.scalar .int)],false⟩ := by
 unfold Plan.headSchema
 rw [show GeneralNominalInspection.queries packet.context.state packet.context.interpretation packet.declaration = _ from query]
 simp [GeneralNominalMaterialization.schemas,GeneralNominalMaterialization.schema,
   GeneralNominalMaterialization.Schema.append,centerSite,displayChild,List.ofFn_succ]

theorem holds (m : Assignment) (valid : Models after m) : Holds plan m := by
 refine ⟨valid.1.1,⟨ordinary m,?_,?_,?_,?_,?_,?_⟩,?_⟩
 · rw [report_exact]
   simp [ProjectionModels]
 · intro i
   exact ⟨subtype_refl _,subtype_refl _⟩
 · intro name used
   rcases used with head | ⟨_,present,_⟩
   · cases head
   · cases present
 · rw [head_schema]
   refine ⟨?_,by intro _ h; cases h⟩
   intro entry seen
   cases List.mem_singleton.mp seen
   refine ⟨⟨_,.source 1⟩,?_⟩
   intro actual observed
   cases observed
   exact valid.1.1.1.2.1 (1 : Fin 2) (.base .int) rfl
 · rw [emitted_empty]
   intro _ found
   cases found
 · intro _ found
   cases found
 · unfold Outputs
   rw [emitted_empty]
   intro _ found
   cases found

end Yulang.GeneralRebaseDisplayChild276
