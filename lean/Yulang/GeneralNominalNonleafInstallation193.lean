import Yulang.GeneralNominalNonleafLocal193

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalNonleafInstallation193
open GeneralNominalNonleafPlan193 GeneralNominalNonleafLocal193
open GeneralNominalExamples (registry context state displayRoot displayChild model state_models)
open GeneralDeclarationExamples (roles)
open GeneralNominalCenteredHeadStepEffects GeneralNominalCenteredHeadStepKernel
open GeneralNominalCenteredHeadOutputs
open GeneralNominalCenteredHeadWFBoundary (boundary)
open GeneralNominalCommonBridge (Assignment)

noncomputable abbrev installedCore := GeneralNominalCenteredSteps.install start.core plan []

theorem installed_requests_empty : requests installedCore displayRoot = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro output member
  obtain ⟨site,present,_,within⟩ := mem_requests_iff.mp member
  change site ∈ start.core.erased.current.sites ++ (GeneralNominalSharedEmission.emitted plan.packet).sites at present
  rcases List.mem_append.mp present with old | fresh
  · cases List.mem_singleton.mp old
    cases within
  · have occurrence : site.occurrence ∈ plan.packet.children := by
      rw [← (GeneralNominalSharedEmission.emitted plan.packet).exact]
      exact List.mem_map.mpr ⟨site,fresh,rfl⟩
    rw [children_exact] at occurrence
    rw [List.mem_singleton.mp occurrence] at within
    cases within

theorem installation_models (assignment : Assignment)
    (valid : GeneralNominalState.Models (state true) assignment) :
    InstallationModels start plan [] assignment := by
  refine ⟨(source_models assignment).mpr valid,holds assignment valid,
    GeneralNominalHeadLeafPlan189.output_equations_empty plan requests_empty assignment,?_,?_⟩
  · exact GeneralNominalHeadLeafPlan189.output_equations_empty
      (state := ⟨installedCore,[]⟩) plan installed_requests_empty assignment
  · intro effect member; cases member

theorem enabled : Installable registry start plan [] := by
  have selectedOld := GeneralNominalCenteredHeadWFBoundary.local_iff.mp selected
  refine ⟨frame,?_,safe,effects_ready,?_,?_,?_,?_,?_,model,installation_models model (state_models true)⟩
  · change GeneralNominalCenteredHeadCandidates.Unique registry (context true) displayRoot 1 plan.packet.children
    rw [children_exact]; exact unique
  · change (GeneralNominalPacketSupport.namedSchema packet).unknown = false
    rw [named_empty]
  · intro prior member; cases member
  · exact GeneralNominalCenteredHeadStepAvailability.selected_initial_value selectedOld frame
  · exact GeneralNominalCenteredHeadStepAvailability.selected_safe selectedOld plan frame.center_recorded
      plan.input_exact frame.registry_eq frame.context_eq frame.visible frame.role_eq frame.prepared frame.located
  · exact GeneralNominalCenteredHeadStepAvailability.selected_alternatives selectedOld plan.input
      frame.center_recorded plan.input_exact

noncomputable abbrev finish := install start plan [] enabled

theorem novel : ¬ GeneralNominalFeedbackSteps.Committed start.core.erased.current plan.packet := by
  intro committed
  have impossible := committed.2 displayChild (by rw [children_exact]; simp)
  cases impossible

theorem actual_step : (boundary roles).Step registry displayRoot start finish :=
  ⟨displayRoot,.root,.install plan [] enabled novel⟩

theorem reachable : B4TargetV6.Reachable (boundary roles) registry displayRoot finish :=
  ⟨start,initial_source,.tail .refl actual_step⟩

theorem final_model : Models finish model :=
  (install_models enabled model).mpr (installation_models model (state_models true))

theorem child_generated : (boundary roles).Generated registry finish displayRoot displayChild := by
  apply GeneralNominalSaturationState.Generated.child .root
  change (displayRoot,displayChild) ∈ [] ++ plan.packet.children.map _
  rw [children_exact]
  simp only [List.nil_append,List.map_cons,List.map_nil,List.mem_singleton]
  rfl

theorem leaf_evidence (assignment : Assignment) (valid : Models finish assignment) :
    (boundary roles).Evidence registry finish assignment displayChild (.node 3 []) := by
  have old : GeneralNominalState.Models (state true) assignment :=
    (source_models assignment).mp ((install_models enabled assignment).mp valid).1
  have rule := GeneralDictionaryOrdinaryTrace.instance_extension registry (context true)
    finish.core.erased.current.context (GeneralDictionaryOrdinaryTrace.packet_extension packet)
    assignment valid.1.1.1 displayChild 3 []
    (GeneralDictionarySupportRecursiveExample.leaf_instance assignment old)
  exact GeneralDictionaryRecursiveEvidence.evidence_node registry _ assignment _ 3 [] [] rule .nil

/-- Both nodes use the same arbitrary final assignment, after a genuine WF installation.
The terminal child is semantic evidence, not a claimed child Installable certificate. -/
theorem recursive_evidence (assignment : Assignment) (valid : Models finish assignment) :
    (boundary roles).Evidence registry finish assignment displayRoot (.node 1 [.node 3 []]) := by
  apply GeneralNominalOrdinaryEvidence191.installed_trace_evidence enabled (root := displayRoot) .refl assignment valid [.node 3 []]
  rw [children_exact]
  exact .cons (leaf_evidence assignment valid) .nil

/-- Nonleaf source-to-evidence soundness on the current WF boundary. This is not
arbitrary V6 EvidenceNode, a final classification, or a stability theorem. -/
theorem source_recursive_sound :
    (boundary roles).Checked registry ∧ (boundary roles).Initial registry displayRoot start ∧
    (boundary roles).Step registry displayRoot start finish ∧
    B4TargetV6.Reachable (boundary roles) registry displayRoot finish ∧
    (boundary roles).Generated registry finish displayRoot displayChild ∧
    Models finish model ∧
    ∀ assignment, Models finish assignment →
      (boundary roles).Evidence registry finish assignment displayRoot (.node 1 [.node 3 []]) :=
  ⟨⟨rfl,GeneralNominalExamples.registry_checked⟩,initial_source,actual_step,reachable,
    child_generated,final_model,recursive_evidence⟩
/-- The emitted packet adds only consequences of the concrete source. No source
model is discarded; this is stronger than exhibiting one final model. -/
theorem final_models_iff (assignment : Assignment) :
    Models finish assignment ↔ GeneralNominalState.Models (state true) assignment := by
  constructor
  · intro valid
    exact (source_models assignment).mp ((install_models enabled assignment).mp valid).1
  · intro valid
    exact (install_models enabled assignment).mpr (installation_models assignment valid)

/-- The source itself already entails both dictionary nodes. The explicit
installation above additionally certifies actual generation, not new assumptions. -/
theorem initial_recursive_evidence (assignment : Assignment) (valid : Models start assignment) :
    (boundary roles).Evidence registry start assignment displayRoot (.node 1 [.node 3 []]) := by
  have finalValid := (final_models_iff assignment).mpr ((source_models assignment).mp valid)
  exact (GeneralNominalOrdinaryEvidence191.evidence_iff
    (.tail .refl (GeneralNominalOrdinaryEvidence191.install_step enabled .root novel))
    assignment finalValid displayRoot (.node 1 [.node 3 []])).mp
      (recursive_evidence assignment finalValid)

/-- The concrete parent was not a leaf; the installation genuinely adds a
child edge that was absent in the source journal. -/
theorem source_not_stable : ¬ (boundary roles).Stable registry start displayRoot := by
  intro stable
  exact stable displayRoot .root finish (.install plan [] enabled novel)

end Yulang.GeneralNominalNonleafInstallation193
