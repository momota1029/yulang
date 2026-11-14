import Yulang.GeneralNominalNonleafReuse193
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalNonleafFinal194
open GeneralNominalNonleafPlan193 GeneralNominalNonleafInstallation193 GeneralNominalNonleafSafety193 GeneralNominalNonleafAdministrative193
open GeneralNominalExamples (registry displayRoot displayChild model)
open GeneralDeclarationExamples (roles display display_checked)
open GeneralDeclarations GeneralNominalCenters GeneralNominalCenteredHeadOutputs
open GeneralNominalCenteredHeadCandidates

noncomputable abbrev parentPacket : GeneralNominalSaturationState.Packet roles :=
  ⟨registry,current,GeneralNominalDemandMerging.pointSite displayRoot,display,display_checked,[((0 : Fin 2),(0 : Fin 2))]⟩
noncomputable abbrev parentPlan : Plan roles := ⟨parentPacket,plan.input,rfl⟩

theorem survivor : Survivor registry current displayRoot 1 [displayChild] := by
  have old := GeneralDictionarySupportRecursiveClassification.parent_selected
  cases old with
  | selected _ unique => exact old_survivor_head unique.1

theorem prepared : Prepared registry current displayRoot display := by
  obtain ⟨_,d,visible,check,key,_,bounds,located,ready,_⟩ := survivor
  simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
  rcases visible with rfl | rfl | rfl
  · cases key
  · exact ready
  · cases key

theorem wrong_failed : Failed registry current displayRoot GeneralNominalExamples.intDisplay := by
  refine ⟨prepared.1,prepared.2.2.1,[((0 : Fin 2),(0 : Fin 2))],rfl,?_,?_,Or.inl ?_⟩ <;> decide +kernel

theorem unique : Unique registry current displayRoot 1 [displayChild] := by
  refine ⟨survivor,?_⟩
  intro key kids found
  have copy := found
  obtain ⟨_,d,visible,check,identity,role,bounds,located,ready,_⟩ := found
  simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
  rcases visible with rfl | rfl | rfl
  · obtain ⟨_,_,_,bs,loc,finished,_⟩ := ready
    have equal := Option.some.inj (loc.symm.trans located)
    subst bs
    have equal := Option.some.inj located
    subst bounds
    exact False.elim ((by decide +kernel : (GeneralNominalRecursiveCandidates.report current GeneralNominalExamples.intDisplay [((0 : Fin 2),(0 : Fin 2))]).conflicts ≠ []) finished.2.1)
  · have same : key = 1 := identity.symm
    subst key
    exact ⟨rfl,survivor_children_functional GeneralNominalExamples.registry_checked copy survivor⟩
  · contradiction

theorem frame : Frame registry finish.core displayRoot 1 parentPlan := by
  refine ⟨rfl,rfl,rfl,rfl,?_,?_,by simp,rfl,rfl,prepared⟩
  · rw [raw_sites]; simp
  · rw [center_sites]; simp

theorem safe : B4TargetV6.SafeKnown (GeneralNominalCenteredHeadWFBoundary.boundary roles) registry finish displayRoot := by
  have old := parent_center_selected
  cases old with
  | selected oldSafe oldUnique =>
    refine ⟨survivor.1,oldSafe.2.1,?_,?_⟩
    · rintro (raw | ⟨_,_,_,_,_,_,_,_,_,_,_,cycle⟩)
      · exact oldSafe.2.2.1 (Or.inl raw)
      · exact centered_acyclic _ cycle
    · rintro (⟨_,d,visible,role,notFailed,notPrepared⟩ | legacy | decision | admin)
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
        rcases visible with rfl | rfl | rfl
        · exact notFailed wrong_failed
        · exact notPrepared prepared
        · contradiction
      · exact oldSafe.2.2.2 (Or.inl (Or.inr legacy))
      · exact decision parent_decision
      · exact admin parent_ready

theorem parent_bindings : parentPacket.bindings = [(0,(1,1))] := by
  have query : GeneralNominalInspection.queries current.state current.interpretation display =
      [.nominal 0 [.variables [0]]] := GeneralNominalNonleafPlan193.query
  have report := GeneralNominalUnaryCaptureFacts.report_exact current display
    (0 : Fin 2) GeneralNominalExamples.listDescriptor rfl 0 ((1 : Fin 2),(1 : Fin 2)) rfl query
  change GeneralNominalRecursiveInspection.bindings _ (GeneralNominalPacketSupport.report parentPacket) = _
  rw [show GeneralNominalPacketSupport.report parentPacket = _ from report]
  rfl

theorem parent_binder : parentPlan.binder 0 = 1 := by
  unfold Plan.binder GeneralNominalPacketSupport.capture
  change (if 0 ∈ display.outputNames then _ else _) = _
  simp only [show ¬ 0 ∈ display.outputNames from by decide +kernel,ite_false]
  rw [parent_bindings]
  rfl

theorem head_equations : HeadEquations parentPlan model := by
  have eqs := GeneralNominalNonleafPlan193.equations model (GeneralNominalExamples.state_models true)
  refine ⟨eqs.1,?_,?_⟩
  · intro name member
    have zero : name = 0 := by
      simpa [parentPlan,parentPacket,Declaration.inputNames,GeneralDeclarationPatterns.variablesArgs,
        GeneralDeclarationPatterns.Pattern.variables,GeneralDeclarationPatterns.normalizeArgs,
        GeneralDeclarationPatterns.normalize] using member
    subst name
    rw [parent_binder]
    change GeneralNominalCaptureMerges.Fits model ((GeneralNominalPacketSupport.capture parentPacket).inputs 0) _
    unfold GeneralNominalPacketSupport.capture
    rw [parent_bindings]
    exact ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩
  · have schema : parentPlan.headSchema = plan.headSchema := rfl
    rw [schema,head_schema]
    have old := eqs.2.2.1
    rw [head_schema] at old
    refine ⟨old.1,?_⟩
    intro entry member
    cases List.mem_singleton.mp member
    simp only [ite_true]
    rw [parent_binder]
    have actual := old.2 ⟨0,origin,.actual⟩ (List.mem_singleton_self _)
    simpa only [ite_true,binder_zero] using actual

theorem no_output_conflict : ¬ GeneralNominalCenteredHeadStepBoundary.OutputConflict registry finish displayRoot 1 := by
  intro conflict
  exact conflict.2 ⟨model,final_model,⟨[displayChild],unique⟩,parentPlan,frame,
    GeneralNominalHeadInitialEffects188.empty_effects_ready (GeneralNominalNonleafReuse193.requests_empty _) parentPlan,
    head_equations,GeneralNominalHeadLeafPlan189.output_equations_empty parentPlan (GeneralNominalNonleafReuse193.requests_empty _) model⟩

theorem selected : GeneralNominalCenteredHeadWFBoundary.Local registry finish displayRoot (.selected 1 [displayChild]) :=
  .selected safe unique no_output_conflict

theorem child_classify : B4TargetV6.Classify (GeneralNominalCenteredHeadWFBoundary.boundary roles) registry finish displayChild (.selected (.node 3 [])) := by
  have localRule := GeneralNominalNonleafReuse193.selected
  cases localRule with
  | selected known chosen clear => exact .selected known chosen clear .nil

theorem parent_classify : B4TargetV6.Classify (GeneralNominalCenteredHeadWFBoundary.boundary roles) registry finish displayRoot (.selected (.node 1 [.node 3 []])) :=
  .selected safe unique no_output_conflict (.cons child_classify .nil)
end Yulang.GeneralNominalNonleafFinal194
