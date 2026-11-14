import Yulang.GeneralNominalRefinementTrace197
import Yulang.GeneralNominalTraceEvidence197

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalRefinementExample197
open GeneralNominalRefinementTrace197
open GeneralNominalTraceRefreshExample197
open GeneralNominalTraceEvidence197 (source_tree source_readback)
open GeneralNominalRefreshFork (state context descriptor)
open GeneralNominalExecutableView196 (next start finish certificate)
open GeneralDeclarationExamples (roles)

theorem nominal_observed : Observed (state none) query (1,1) := by
  change Observed (state none) (.nominal 0 [.nominal 0 [.variables [0]]]) ((1 : Fin 5),1)
  apply Observed.point (state := state none) (slot := (1 : Fin 5))
    (descriptor := descriptor (2,2)) (actuals := [(2,2)]) rfl rfl rfl
  apply ObservedMany.cons
  · apply Observed.point (state := state none) (slot := (2 : Fin 5))
      (descriptor := descriptor (3,3)) (actuals := [(3,3)]) rfl rfl rfl
    exact .cons .variables .nil
  · exact .nil

theorem tree_observed : TreeObserved registry (context none) tree := by
  apply TreeObserved.node
  · intro decl member _ bounds located
    have same := List.mem_singleton.mp member
    subst decl
    have same := Option.some.inj (lookup.symm.trans located)
    subst bounds
    rw [computed_query]
    exact .cons nominal_observed .nil
  · intro child member; cases member

/-- Unlike the first fixture, this application provides no observations about
next. They are deduced from the actual source-preserving refresh certificate. -/
theorem final_payload (wide : Bool) (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalCenteredHeadStepEffects.Models (finish wide) model) :
    (GeneralNominalCenteredHeadWFBoundary.boundary roles).Evidence registry (finish wide)
      model focus payload :=
  universal_refresh (state := start) (next := next wide) (certificate wide) tree_observed
    source_readback (fun m hm => source_tree m hm.1.1.1) model valid

/-- The nonpoint constructor checks both old descriptors and both argument
lists, not just the lower endpoint. -/
theorem interval_observed : Observed (state none) (.nominal 0 [.variables [0]]) (1,2) := by
  apply Observed.interval (state := state none) (bounds := ((1 : Fin 5),2))
    (lower := descriptor (2,2)) (upper := descriptor (3,3))
    (left := [(2,2)]) (right := [(3,3)]) (by decide +kernel) rfl rfl rfl rfl rfl rfl
  · exact .cons .variables .nil
  · exact .cons .variables .nil

theorem interval_report (wide : Bool) :
    GeneralNominalRecursiveInspection.inspect
      (GeneralNominalViewTransport196.replace (state none) (next wide))
      (.nominal 0 [.variables [0]]) ((1 : Fin 5), (2 : Fin 5)) none =
    GeneralNominalViewTransport196.report (next wide)
      (GeneralNominalRecursiveInspection.inspect (state none)
        (.nominal 0 [.variables [0]]) (1,2) none) :=
  GeneralNominalInspectionTrace197.trace_report
    (GeneralNominalRefinementTrace197.traced (certificate wide).refines interval_observed) none
end Yulang.GeneralNominalRefinementExample197
