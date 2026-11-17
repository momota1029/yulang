import Yulang.GeneralDictionaryMixedGap206Selected234
import Yulang.GeneralNominalVersionedMixedTerminalStable234
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryMixedGap206Stable234
open GeneralDictionaryDefaultGap206Source (roles registry root model counter)
open GeneralDictionaryVersionedGap206Feedback234 (feedback)
open GeneralDictionaryMixedGap206Refresh234 (refreshed model_retained)
open GeneralDictionaryMixedGap206Frame234
open GeneralNominalVersionedJournal232 GeneralNominalVersionedMixedKernel234

theorem raw_to_models (assignment) (valid : GeneralNominalState.Models refreshed.core.erased.current.context.state assignment) :
    Models refreshed assignment :=
  (GeneralDictionaryMixedGap206Refresh234.models_iff assignment).mpr
    (GeneralDictionaryVersionedGap206AfterStable234.raw_to_models assignment
      (GeneralNominalRefinements.models GeneralDictionaryMixedGap206Snapshot234.refines assignment valid))

theorem headless : GeneralNominalVersionedMixedTerminalStable234.HeadlessUnknown refreshed := by
  refine ⟨model,model_retained,?_⟩
  intro identity member unknown test
  have bound : ∀ name ∈ GeneralNominalState.sources refreshed.core.erased.current.context.state, name < 3 := by
    decide +kernel
  have known : GeneralNominalState.Known refreshed.core.erased.current.context.state identity :=
    ⟨⟨identity,bound identity member⟩,rfl,Or.inl (by intro impossible; cases impossible)⟩
  exact False.elim (unknown known)

theorem committed : Committed refreshed plan := by
  refine ⟨fun assignment valid => ⟨packet_holds assignment valid,
    GeneralDictionaryMixedGap206Evidence234.class_effects assignment valid⟩,?_⟩
  intro child member
  rw [children_empty] at member
  cases member

theorem stable : Stable registry refreshed root := by
  apply GeneralNominalVersionedMixedTerminalStable234.stable raw_sites centers
    GeneralDictionaryMixedGap206Selected234.edges_empty
    (by intro slot descriptor recorded; cases recorded) headless
  · intro first last _ _ equal assignment valid
    exact equal assignment (raw_to_models assignment valid)
  · intro effect enabled same
    have framed := same ▸ enabled.snapshot_eq ▸ enabled.registry_eq ▸ effect.frame
    have planEq := GeneralDictionaryMixedGap206Selected234.frame_plan framed
    exact planEq.symm ▸ committed

theorem regression :
    B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root refreshed ∧
    Models refreshed model ∧ ¬ Models refreshed counter ∧ Stable registry refreshed root ∧
    GeneralNominalVersionedMixedSourceBoundary234.Local registry refreshed root (.selected 37 []) ∧
    B4SkeletonV8.EvidenceAt (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry refreshed root ∧
    ∀ assignment, Models refreshed assignment → GeneralNominalVersionedEvidence231.Evidence registry refreshed.core assignment root (.node 37 []) :=
  ⟨GeneralDictionaryMixedGap206Refresh234.reachable,model_retained,
    GeneralDictionaryMixedGap206Refresh234.counter_removed,stable,
    GeneralDictionaryMixedGap206Selected234.selected,GeneralDictionaryMixedGap206Selected234.evidenceAt,
    GeneralDictionaryMixedGap206Evidence234.evidence⟩

end Yulang.GeneralDictionaryMixedGap206Stable234
