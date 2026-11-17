import Yulang.GeneralDictionaryMixedGround218FinalState235
import Yulang.GeneralDictionaryMixedGround218PointInstalledShape235
import Yulang.GeneralDictionaryMixedGround218FinalEvidence235
set_option backward.isDefEq.respectTransparency false
/-! Original source to a nonempty full-mixed Stable endpoint with literal
EvidenceAt and generated selected children. Only this concrete 218 regression is
claimed; the equality endpoint is proof-level, not an executable general driver. -/
namespace Yulang.GeneralDictionaryMixedGround218FinalRegression235
open GeneralDictionaryGroundCopy218Source
open GeneralDictionaryMixedGround218FinalState235
open GeneralNominalVersionedJournal232 GeneralNominalVersionedMixedKernel234

theorem sites : GeneralDictionaryMixedGround218PointStable235.Sites finalState := by
  rw [GeneralNominalVersionedMixedEqualityClosure235.trace_shape equality_path]
  exact GeneralDictionaryMixedGround218PointInstalledShape235.sites

theorem stable : Stable registry finalState root :=
  GeneralDictionaryMixedGround218RootCommitted235.stable sites recorded allocated reserved ordinary
    final_context final_model equalities

theorem no_step (after : State roles) : ¬ Step registry root finalState after := by
  rintro ⟨focus,generated,action⟩
  exact stable focus generated after action

theorem children_stable {child : GeneralSourceDictionaries.Occurrence roles} (generated : GeneralNominalSaturationState.Generated finalState.core.erased.current root child) :
    Stable registry finalState child :=
  fun focus path => stable focus (GeneralNominalSaturationState.generated_trans generated path)

theorem evidenceAt : B4SkeletonV8.EvidenceAt (GeneralNominalVersionedMixedSourceBoundary234.boundary roles)
    sourceRegistry finalState root :=
  GeneralDictionaryMixedGround218FinalEvidence235.evidenceAt
    GeneralDictionaryMixedGround218FinalState235.reachable sites recorded allocated reserved ordinary final_context

theorem generated_children {child : GeneralSourceDictionaries.Occurrence roles}
    (reached : demand = root ∨ GeneralNominalSaturationState.Generated finalState.core.erased.current root demand)
    (selected : GeneralNominalVersionedMixedSourceBoundary234.Local sourceRegistry finalState demand (.selected key children))
    (member : child ∈ children) : GeneralNominalSaturationState.Generated finalState.core.erased.current root child :=
  GeneralDictionaryMixedGround218FinalEvidence235.generated_children
    GeneralDictionaryMixedGround218FinalState235.reachable sites recorded allocated reserved ordinary final_context
    ⟨_,final_model⟩ reached selected member

theorem source_regression :
    (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Checked sourceRegistry ∧
    B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) sourceRegistry root finalState ∧
    (∃ model, Models finalState model) ∧ Stable registry finalState root ∧
    B4SkeletonV8.EvidenceAt (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) sourceRegistry finalState root :=
  ⟨⟨rfl,source_checked⟩,GeneralDictionaryMixedGround218FinalState235.reachable,⟨_,final_model⟩,stable,evidenceAt⟩

end Yulang.GeneralDictionaryMixedGround218FinalRegression235
