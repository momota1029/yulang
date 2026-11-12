import Yulang.GeneralNominalSupportExamples
import Yulang.GeneralDictionaryOrdinaryTrace

/-! A real source-supported Display(List Int) installation and a complete
recursive semantic dictionary in its final context. The existing visible
terminal Int key is 3. No stable final executor result is asserted. -/
namespace Yulang.GeneralDictionarySupportRecursiveExample
open GeneralNominalExamples
open GeneralDeclarationExamples (roles display display_checked)
open GeneralDeclarations GeneralNominalSaturationState
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralDictionaryRecursiveEvidence (Instance Evidence)

abbrev start := GeneralNominalSupport.initial (context true) displayRoot
abbrev packet : Packet roles := ⟨registry,context true,GeneralNominalDemandMerging.pointSite displayRoot,
  display,display_checked,[(0,0)]⟩
noncomputable abbrev finish := GeneralNominalSupportSteps.install start packet []

private theorem prepared : Prepared registry (context true) displayRoot display display_checked := by
  obtain ⟨_,decl,visible,checked,key,_,_,_,ready,_⟩ := GeneralNominalRecursiveExamples.display_survivor
  simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
  rcases visible with rfl | rfl | rfl
  · contradiction
  · exact ready
  · contradiction

theorem children_exact : packet.children = [displayChild] := by
  obtain ⟨_,decl,visible,checked,key,_,bounds,located,_,emitted⟩ := GeneralNominalRecursiveExamples.display_survivor
  simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
  rcases visible with rfl | rfl | rfl
  · contradiction
  · have same := Option.some.inj located
    subst bounds
    exact emitted.symm
  · contradiction

theorem enabled : GeneralNominalFeedbackSteps.Installable registry start.current packet := by
  have selected := GeneralNominalSupportBoundary.selected_old GeneralNominalSupportExamples.display_selected
  have localRule : GeneralNominalFeedbackK2.Local registry start.current displayRoot
      (.selected display.id packet.children) := by rw [children_exact]; exact selected
  obtain ⟨_,_,_,bounds,located,_,_,m,branch⟩ := prepared
  have same := Option.some.inj located
  subst bounds
  refine ⟨⟨rfl,rfl,by simp [start,GeneralNominalSupport.initial,initial],by simp,rfl,rfl,prepared,
    GeneralNominalFeedbackK2.selected_legacy localRule,?_,?_,?_,?_⟩,localRule,?_⟩
  · intro prior member; cases member
  · intro other member _
    have same := List.mem_singleton.mp member; subst other; exact .refl _
  · exact ⟨m,(initial_models ..).mpr (branch_interval_sound _ _ _ _ _ _ _ branch).1,branch⟩
  · exact GeneralNominalJointCandidates.initial_joint registry (context true) displayRoot display
      (by simp) display_checked rfl [(0,0)] rfl prepared m branch
  · intro other member _
    have same := List.mem_singleton.mp member; subst other; exact .refl _

theorem actual_step : GeneralNominalSupportSteps.Step registry displayRoot start finish := by
  refine ⟨displayRoot,.root,.install packet [] enabled ?_ GeneralNominalSupportExamples.display_guard⟩
  intro committed
  have missing := committed.2 displayChild (by rw [children_exact]; simp)
  cases missing

theorem initial_source : GeneralNominalSourceFormation.InitialSource registry (context true) displayRoot where
  roles_agree := rfl
  metadata := prepared.1
  linked := prepared.2.1
  intervals := fun _ _ _ => CommonNominalFullCarrier.subtype_refl _
  below_seed := by
    intro source member
    have small : source = 0 ∨ source = 1 := by
      simp [GeneralNominalState.sources,List.ofFn_succ] at member
      rcases member with h | h | h | h <;> simp [h]
    rcases small with rfl | rfl <;> decide +kernel
  unallocated := rfl

theorem actual_reachable : B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles)
    registry displayRoot finish := ⟨start,⟨context true,initial_source,rfl⟩,.tail .refl actual_step⟩

theorem parent_instance (m : GeneralNominalCommonBridge.Assignment) (valid : Models finish.current m) :
    Instance registry finish.current.context m displayRoot 1 [displayChild] := by
  have instanceRule := GeneralDictionaryOrdinaryTrace.installed_trace_current_instance registry displayRoot
    start.current finish.current packet enabled .refl m valid
  change Instance registry finish.current.context m displayRoot 1 packet.children at instanceRule
  rw [children_exact] at instanceRule
  exact instanceRule

private theorem leaf_report : report (context true) intDisplay [(1,1)] =
    { inspected := [(1,1)], checked := [(1,1),(1,1)] } := by
  simp [report,GeneralNominalInspection.queries,Declaration.normalHead,
    GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
    GeneralNominalInspection.translate,GeneralNominalExamples.interpretation,
    inspectMany,inspect,Report.visit,Report.append]

private theorem leaf_schema : generated registry (context true) displayChild intDisplay int_display_checked [(1,1)] = {} := by
  cbv

private theorem leaf_branch (m : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models (state true) m) :
    BranchModels registry (context true) displayChild intDisplay int_display_checked [(1,1)] m := by
  refine ⟨?_,?_,?_⟩
  · unfold privateState
    rw [leaf_report]
    apply (GeneralNominalState.extend_models ..).mpr
    refine ⟨(GeneralNominalAllocation.propagate_models ..).mpr ⟨valid,?_,?_⟩,?_⟩
    · simp [bindings,GeneralNominalAllocation.Compatible]
    · simp [bindings,GeneralNominalAllocation.merges,Declaration.inputNames,
        GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
        GeneralDeclarationPatterns.variablesArgs,GeneralDeclarationPatterns.Pattern.variables]
    · simp [selfChecks,PresenceNormalForm.All]
      exact CommonNominalFullCarrier.subtype_refl _
  · rw [leaf_report]
    simp [ProjectionModels]
  · rw [leaf_schema]
    simp [GeneralNominalMaterialization.Models]

theorem leaf_instance (m : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models (state true) m) :
    Instance registry (context true) m displayChild 3 [] := by
  refine ⟨intDisplay,by simp,int_display_checked,rfl,rfl,[(1,1)],?_,?_,?_,?_,prepared.1,leaf_branch m valid⟩
  · decide +kernel
  · rw [leaf_report]; exact ⟨rfl,rfl,rfl⟩
  · refine ⟨?_,?_⟩
    · intro output member; cases member
    · rw [leaf_schema]
  · cbv

theorem final_leaf_evidence (m : GeneralNominalCommonBridge.Assignment) (valid : Models finish.current m) :
    Evidence registry finish.current.context m displayChild (.node 3 []) := by
  have old := ((GeneralNominalFeedbackSites.install_models start.current packet
    (GeneralNominalFeedbackSites.emitted packet) rfl m).mp valid).1.1
  have rule := GeneralDictionaryOrdinaryTrace.instance_extension registry (context true)
    finish.current.context (GeneralDictionaryOrdinaryTrace.packet_extension packet) m valid.1
    displayChild 3 [] (leaf_instance m old)
  exact GeneralDictionaryRecursiveEvidence.evidence_node registry finish.current.context m displayChild 3 [] [] rule .nil

/-- Both nodes are interpreted in the same arbitrary final journal model. -/
theorem final_recursive_evidence (m : GeneralNominalCommonBridge.Assignment) (valid : Models finish.current m) :
    Evidence registry finish.current.context m displayRoot (.node 1 [.node 3 []]) :=
  GeneralDictionaryRecursiveEvidence.evidence_node registry finish.current.context m displayRoot 1 [displayChild]
    [.node 3 []] (parent_instance m valid) (.cons (final_leaf_evidence m valid) .nil)

theorem nonempty_journal : finish.current.packets ≠ [] := by
  change packet :: start.current.packets ≠ []
  simp

theorem final_inhabited : ∃ m, Models finish.current m := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,⟨m,valid,branch⟩,_⟩ := enabled.1
  exact ⟨m,(GeneralNominalFeedbackSites.install_models start.current packet
    (GeneralNominalFeedbackSites.emitted packet) rfl m).mpr ⟨valid,branch⟩⟩

/-- A positive recursive semantic dictionary after an actual initial support
step; neither a fabricated journal nor a plan-only readback certificate. -/
theorem nonvacuous_recursive_dictionary :
    B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry displayRoot finish ∧
    finish.current.packets ≠ [] ∧ ∃ m, Models finish.current m ∧
      Evidence registry finish.current.context m displayRoot (.node 1 [.node 3 []]) := by
  obtain ⟨m,valid⟩ := final_inhabited
  exact ⟨actual_reachable,nonempty_journal,m,valid,final_recursive_evidence m valid⟩

end Yulang.GeneralDictionarySupportRecursiveExample
