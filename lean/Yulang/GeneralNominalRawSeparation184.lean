import Yulang.GeneralNominalGeneratedSupport184
import Yulang.GeneralNominalGroundSiteSupport184
import Yulang.GeneralNominalModeLedger181

/-! Complete raw-journal namespace exclusion for the original centered ground
boundary. The centered ledger is intentionally not included in this footprint. -/
namespace Yulang.GeneralNominalRawSeparation184
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralNominalCenteredGroundBoundary (groundBoundary)
open GeneralNominalCommonBridge (Assignment)

theorem ground_raw_separate
    (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (high : 7 ≤ purpose) :
    fresh state.erased.current.context.state.seed invocation declaration purpose owner position ∉
      GeneralNominalRawFrame179.rawSources state.erased.current := by
  intro present
  rcases List.mem_append.mp present with present | present
  · rcases List.mem_append.mp present with present | present
    · obtain ⟨start,⟨context,labels,source,point,ground,rfl⟩,path⟩ := reachable
      rw [(GeneralNominalCenteredTrace.configuration_trace path).1] at present
      exact GeneralNominalCenteredAllocation.fresh_outside_raw_sources source
        (GeneralNominalCenteredAncestry.installed_depth_bound point ground) path high present
    · obtain ⟨packet,member,present⟩ := List.mem_flatMap.mp present
      exact GeneralNominalGeneratedSupport184.ground_packet_separate reachable packet member high present
  · obtain ⟨site,member,present⟩ := List.mem_flatMap.mp present
    exact GeneralNominalGroundSiteSupport184.ground_sites_separate reachable site member high present

theorem raw_assign_preserves
    (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (names : Fin count → Nat) (values : Fin count → CommonNominalFullCarrier.Ty)
    (allocated : ∀ index, ∃ invocation declaration purpose owner position, 7 ≤ purpose ∧
      names index = fresh state.erased.current.context.state.seed invocation declaration purpose owner position)
    (model : Assignment) (valid : GeneralNominalSaturationState.Models state.erased.current model) :
    GeneralNominalSaturationState.Models state.erased.current
      (GeneralNominalCenteredModelExtension.assign model names values) := by
  apply GeneralNominalRawFrame179.raw_models_frame state.erased.current _ valid
  apply GeneralNominalCenteredFrame179.assign_agree
  intro index
  obtain ⟨invocation,declaration,purpose,owner,position,high,equal⟩ := allocated index
  rw [equal]
  exact ground_raw_separate reachable high

theorem overlap_iff_ledger
    (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (high : 7 ≤ purpose) :
    fresh state.erased.current.context.state.seed invocation declaration purpose owner position ∈
      GeneralNominalModeLedger181.fullSources state ↔
    fresh state.erased.current.context.state.seed invocation declaration purpose owner position ∈
      GeneralNominalModeLedger181.ledgerSources state := by
  exact List.mem_append.trans (or_iff_right (ground_raw_separate reachable high))

end Yulang.GeneralNominalRawSeparation184
