import Yulang.GeneralNominalReusableForest192
import Yulang.GeneralNominalCenteredPointMergeExample
import Yulang.GeneralNominalCenteredHeadWFFixtures
import Yulang.GeneralNominalSharedExamples

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalNonleafPlan193
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalRecursiveInspection
open GeneralNominalCenters
open GeneralDeclarationExamples (roles display display_checked)
open GeneralNominalExamples (context state displayRoot displayChild listDescriptor interpretation model state_models registry)
open CommonNominalFullCarrier
abbrev declaration := display
abbrev packet := GeneralDictionarySupportRecursiveExample.packet
abbrev origin : Origin := .nominal (.source 0) 0 0
abbrev start := GeneralNominalCenteredHeadStepEffects.initial (context true) displayRoot
abbrev plan : Plan roles := ⟨packet,rootSite (state true).seed displayRoot,rfl⟩
theorem query : GeneralNominalInspection.queries (state true) interpretation declaration = [.nominal 0 [.variables [0]]] := by
  simp [GeneralNominalInspection.queries,Declaration.normalHead,
    GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
    GeneralNominalInspection.translate,interpretation]
theorem raw_report : GeneralNominalPacketSupport.report packet =
    GeneralNominalUnaryCaptureFacts.captured (state true) 0 0 0 (1,1) :=
  GeneralNominalUnaryCaptureFacts.report_exact (context true) declaration 0 listDescriptor rfl 0 (1,1) rfl query

theorem inherited : (GeneralNominalSharedCaptures.inheritedReport packet).captures = [⟨0,(1,1),some origin⟩] := by
  unfold GeneralNominalSharedCaptures.inheritedReport
  rw [query]
  simp [inspectMany,inspect,GeneralNominalExamples.state,GeneralNominalExamples.listDescriptor,
    typeArguments,Report.visit,Report.append,packet,GeneralNominalDemandMerging.pointSite,
    displayRoot,GeneralNominalExamples.displayDemand,roles,GeneralDeclarationExamples.bareRole,List.ofFn_succ,origin]
  repeat first
    | rw [inspectMany.eq_def]
    | rw [inspect.eq_def]
    | simp [Report.append]

theorem bindings : packet.bindings = [(0,(1,1))] := by
  change GeneralNominalRecursiveInspection.bindings _ (GeneralNominalPacketSupport.report packet) = _
  rw [raw_report]
  rfl

theorem binder_zero : plan.binder 0 = 1 := by
  unfold Plan.binder GeneralNominalPacketSupport.capture
  change (if 0 ∈ declaration.outputNames then _ else _) = _
  simp only [show ¬ 0 ∈ declaration.outputNames from by decide +kernel,ite_false]
  rw [bindings]
  rfl

theorem named_empty : GeneralNominalPacketSupport.namedSchema packet = {} := GeneralNominalRecursiveExamples.display_schema registry (context true) displayRoot rfl display_checked [(0,0)]

theorem input_empty : GeneralNominalPacketSupport.inputSchema packet = {} :=
  GeneralNominalSharedExamples.input_empty false

theorem head_schema : plan.headSchema =
    ⟨[⟨0,origin,.actual⟩],[(.source 0,.nominal 0 1)],false⟩ := by
  unfold Plan.headSchema
  rw [query]
  simp [GeneralNominalMaterialization.schemas,GeneralNominalMaterialization.schema,
    GeneralNominalMaterialization.Schema.append,plan,rootSite,displayRoot,
    GeneralNominalExamples.displayDemand,roles,GeneralDeclarationExamples.bareRole,List.ofFn_succ,origin]

def centerSite : Site roles := ⟨displayChild,fun _ => 1⟩

theorem first_child : plan.childSite GeneralDeclarationExamples.displayChild
    (display_checked.signature.2.2.2 _ (by simp)) = centerSite := by
  unfold Plan.childSite centerSite
  congr 1
  · unfold GeneralNominalFeedbackSites.clauseChild GeneralNominalFeedbackSites.frame GeneralNominalAllocation.frame
    change GeneralDictionaryEmissionPlans.occurrence _ _ = _
    rw [show plan.packet = packet from rfl,bindings]
    simp [GeneralDictionaryEmissionPlans.occurrence,GeneralDeclarationDemands.emit,
      GeneralDeclarationDemands.childDemand,GeneralDeclarationDemands.inputInterval,
      GeneralNominalAllocation.capture,GeneralNominalAllocation.occurrences,
      GeneralDeclarationPatterns.normalize,displayChild,packet,displayRoot,GeneralNominalDemandMerging.pointSite,
      GeneralDeclarationExamples.displayChild]
  · funext index
    have zero : index.val = 0 := by have bound := index.isLt; change index.val < 1 at bound; omega
    simpa only [zero,GeneralDeclarationExamples.displayChild,List.getElem_cons_zero,
      Plan.emittedCenter,GeneralDeclarationPatterns.normalize] using binder_zero

private theorem fit_length {base : GeneralSourceState.State} {m : GeneralNominalCommonBridge.Assignment}
    {parameters : List (GeneralNominalState.Parameter base.slots)} {values : List CommonNominalFullCarrier.Argument}
    (fit : GeneralNominalState.FitsAll base m parameters values) : parameters.length = values.length := by
  induction fit with
  | nil => rfl
  | cons head rest ih => exact congrArg Nat.succ ih

theorem equations (m : GeneralNominalCommonBridge.Assignment) (valid : GeneralNominalState.Models (state true) m) : plan.Equations m := by
  have seen := nominal_argument_bounds (state true) m valid 0 listDescriptor rfl 0 (1,1) rfl
  have actual : GeneralNominalOriginTerms.Same m origin (.source 1) := by
    refine ⟨seen.1,⟨_,.source 1⟩,?_⟩
    intro a b ha hb
    cases hb
    exact ⟨(seen.2 a ha).2,(seen.2 a ha).1⟩
  refine ⟨point_root_holds _ displayRoot (fun _ => rfl) m,?_,?_,?_,?_,?_⟩
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
    rw [binder_zero]
    change GeneralNominalCaptureMerges.Fits m ((GeneralNominalPacketSupport.capture packet).inputs 0) _
    unfold GeneralNominalPacketSupport.capture
    rw [bindings]
    exact ⟨subtype_refl _,subtype_refl _⟩
  · rw [head_schema]
    constructor
    · intro entry member
      cases List.mem_singleton.mp member
      have nominal := GeneralNominalState.nominal_models (state true) m valid 0 listDescriptor rfl
      obtain ⟨arguments,fit,equal⟩ := nominal
      exact ⟨⟨_,.source 0⟩,by intro value observed; cases observed; exact ⟨arguments,by exact (fit_length fit).symm,equal⟩⟩
    · intro entry member
      cases List.mem_singleton.mp member
      simp only [ite_true]
      rw [binder_zero]
      exact actual
  · rw [show plan.packet = packet from rfl,input_empty]
    exact ⟨(by intro _ impossible; cases impossible),(by intro _ impossible; cases impossible)⟩
  · rw [show plan.packet = packet from rfl,named_empty]
    exact ⟨(by intro _ impossible; cases impossible),(by intro _ impossible; cases impossible)⟩
  · intro clause member signature
    change clause ∈ declaration.requirements at member
    cases List.mem_singleton.mp member
    all_goals
      constructor
      · rw [first_child]
        intro index
        exact ⟨subtype_refl _,subtype_refl _⟩
      · change plan.SchemaHolds (GeneralNominalMaterialization.generated _ _
          [⟨.var 0,plan.binder 0,.actual⟩]) m
        simp only [GeneralNominalMaterialization.generated,GeneralNominalMaterialization.schema,
          GeneralNominalMaterialization.Schema.append,GeneralNominalInspection.translate,
          GeneralDeclarationPatterns.normalize,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,
          List.append_nil,Plan.SchemaHolds]
        refine ⟨(by intro _ impossible; cases impossible),?_⟩
        intro entry member
        cases List.mem_singleton.mp member
        exact GeneralNominalOriginTerms.source_self m _


theorem branch (m : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models (state true) m) : packet.Holds m := by
  have result := GeneralNominalUnaryCaptureFacts.private_models (context true) registry displayRoot display
    0 listDescriptor rfl 0 rfl (1,1) rfl query m valid
  refine ⟨result.1,result.2,?_⟩
  change GeneralNominalMaterialization.Models _ _ _ _ (GeneralNominalPacketSupport.namedSchema packet) m
  rw [named_empty]
  exact GeneralNominalMaterialization.empty_models ..

theorem holds (m : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models (state true) m) : plan.Holds m :=
  ⟨branch m valid,equations m valid⟩

theorem children_exact : plan.packet.children = [displayChild] :=
  GeneralDictionarySupportRecursiveExample.children_exact

theorem initial_source : (GeneralNominalCenteredHeadWFBoundary.boundary roles).Initial registry displayRoot start :=
  GeneralNominalCenteredHeadWFFixtures.display_initial

theorem source_models (m : GeneralNominalCommonBridge.Assignment) :
    GeneralNominalCenteredHeadStepEffects.Models start m ↔ GeneralNominalState.Models (state true) m := by
  rw [GeneralNominalCenteredHeadStepEffects.initial_models]
  exact GeneralNominalCenteredSteps.point_initial_models _ _ (fun _ => rfl) m

end Yulang.GeneralNominalNonleafPlan193
