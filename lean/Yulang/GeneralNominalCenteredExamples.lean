import Yulang.GeneralNominalCenteredBoundary
import Yulang.GeneralNominalActualInspectionExamples
import Yulang.GeneralNominalGroundExamples

/-! Concrete center sharing for the checked interval trigger, and preserved
point-source meaning and Display/Wrap local outcomes. The consequences required from a trigger
trace remain explicit premises of the final K2 classification theorem. -/
namespace Yulang.GeneralNominalCenteredExamples
open GeneralNominalCenters GeneralNominalCenteredSteps GeneralNominalCenteredBoundary
open GeneralNominalSettledIntervalDeclarations GeneralNominalSettledIntervalSource

abbrev triggerPlan : Plan roles :=
  ⟨GeneralNominalSharedPump.pPacket,rootSite source.seed root,rfl⟩

theorem trigger_generation : GenerationGuard triggerPlan := generation_guard triggerPlan

theorem trigger_old_generation_missing :
    ¬ GeneralNominalSharedCaptures.GenerationGuard start triggerPlan.packet :=
  GeneralNominalSharedPump.p_first_round_blocked start

theorem trigger_b_shared :
    (triggerPlan.childSite wrapChild (p_checked.signature.2.2.2 wrapChild (by simp))).center ⟨1,by decide +kernel⟩ =
    (triggerPlan.childSite recurChild (p_checked.signature.2.2.2 recurChild (by simp))).center ⟨1,by decide +kernel⟩ := rfl

theorem trigger_b_center_named : (rootSite source.seed root).center ⟨1,by decide +kernel⟩ > source.seed :=
  nonpoint_center_fresh _ _ _ (by decide +kernel)

theorem trigger_b_agrees (model : GeneralNominalCommonBridge.Assignment) (valid : triggerPlan.Holds model) :
    GeneralNominalOriginTerms.Same model
      (.source ((rootSite source.seed root).center ⟨1,by decide +kernel⟩)) (.source (triggerPlan.binder 1)) := by
  apply capture_agreement triggerPlan 1 model valid
    (⟨1,.source ((rootSite source.seed root).center ⟨1,by decide +kernel⟩),.actual⟩ : GeneralNominalMaterialization.Use) _ rfl rfl
  change _ ∈ (GeneralNominalMaterialization.schemas _ _ _ _).variables
  rw [GeneralNominalSharedPump.p_queries]
  simp [GeneralNominalMaterialization.schemas,GeneralNominalMaterialization.schema,
    GeneralNominalMaterialization.Schema.append,triggerPlan,rootSite,root,roles,bareRole,
    GeneralNominalProvenanceDeclarations.bareRole,List.ofFn_succ]

abbrev triggerLeafPlan : Plan roles :=
  ⟨GeneralNominalSharedPump.leaf,
    rootSite source.seed GeneralNominalSettledIntervalOutputs.leafRoot,rfl⟩

theorem trigger_leaf_output_certificate :
    Nonempty (GeneralNominalCenteredSupport.OutputCertificate triggerLeafPlan) :=
  GeneralNominalCenteredSupport.output_certificate_total triggerLeafPlan

open GeneralNominalExamples (displayRoot wrapRoot displayChild wrapChild)

theorem display_initial_models (model : GeneralNominalCommonBridge.Assignment) :
    Models (initial (GeneralNominalExamples.context true) displayRoot) model ↔
      GeneralNominalState.Models (GeneralNominalExamples.state true) model :=
  point_initial_models _ _ (fun _ => rfl) model

theorem wrap_initial_models (model : GeneralNominalCommonBridge.Assignment) :
    Models (initial (GeneralNominalExamples.context true) wrapRoot) model ↔
      GeneralNominalState.Models (GeneralNominalExamples.state true) model :=
  point_initial_models _ _ (fun _ => rfl) model

theorem show_initial_models (model : GeneralNominalCommonBridge.Assignment) :
    Models (initial GeneralNominalGroundExamples.context GeneralNominalGroundExamples.root) model ↔
      GeneralNominalState.Models GeneralNominalGroundExamples.source model :=
  point_initial_models _ _ (fun _ => rfl) model

theorem show_initial_inhabited :
    Models (initial GeneralNominalGroundExamples.context GeneralNominalGroundExamples.root) GeneralNominalGroundExamples.witness :=
  (show_initial_models _).mpr GeneralNominalGroundExamples.inhabited

theorem display_selected : Local GeneralNominalExamples.registry
    (initial (GeneralNominalExamples.context true) displayRoot) displayRoot (.selected 1 [displayChild]) := by
  apply selected_of_old (GeneralNominalSupportBoundary.selected_old GeneralNominalSupportExamples.display_selected)
  · exact initial_acyclic _ _ (GeneralNominalActualInspectionExamples.acyclic false)
  · exact GeneralNominalCenteredSupport.legacy_decision GeneralNominalSharedExamples.display_guard.2.1

theorem wrap_selected : Local GeneralNominalExamples.registry
    (initial (GeneralNominalExamples.context true) wrapRoot) wrapRoot (.selected 2 [GeneralNominalExamples.wrapChild]) := by
  apply selected_of_old (GeneralNominalSupportBoundary.selected_old GeneralNominalSupportExamples.wrap_selected)
  · exact initial_acyclic _ _ (GeneralNominalActualInspectionExamples.acyclic true)
  · exact GeneralNominalCenteredSupport.legacy_decision GeneralNominalSharedExamples.wrap_guard.2.1

/-- Producing these equations and the recorded edge by an InitialSource trace
is separate from the local outcome proved here. -/
theorem trigger_rejected_of_trace_constraints
    (state : State roles) (site : Site roles) (demand : GeneralSourceDictionaries.Occurrence roles)
    (registered : site ∈ state.sites) (same : site.occurrence = demand)
    (index : Fin (roles site.occurrence.demand.role).arity) (a next out : Nat)
    (known : ¬ (fields roles).RootPending registry state demand)
    (equations : ∀ model, Models state model →
      CommonNominalFullCarrier.Equivalent (model a).1 (V (model (site.center index)).1) ∧
      CommonNominalFullCarrier.Equivalent (model a).1 (V (model next).1) ∧
      CommonNominalFullCarrier.Equivalent (model next).1 (V (model (site.center index)).1) ∧
      CommonNominalFullCarrier.Equivalent (model out).1 (model a).1)
    (edge : GeneralNominalCenteredGraph.Recorded (graph state) (.source out) child)
    (shared : GeneralNominalCenteredGraph.Equal (graph state) child (.source (site.center index)))
    (inhabited : ∃ model, Models state model) : Local registry state demand .rejected :=
  root_cycle_rejected known ⟨site,registered,same,index,Or.inr
    (GeneralNominalCenteredGraph.trigger_k2 (graph state) a (site.center index) next out equations edge shared inhabited)⟩

end Yulang.GeneralNominalCenteredExamples
