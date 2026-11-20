import Yulang.GeneralRebaseRowLedgerFirst288

/-! Raw address listing is strictly larger than the set that this fixture's
trust can recognize. The particular extra address is an actual reserved key,
not an invented arbitrary identifier. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 15000000
namespace Yulang.GeneralRebaseRowLedgerNames288
open GeneralRebaseRowChildSource287
open GeneralRebaseRowParentPacket287 (packet plan)
open GeneralRebaseRowLedger288 (supplemented)
open GeneralNominalVersionedMixedObservations233 (Refresh)

abbrev privateKey :=
  GeneralNominalAggregateVersion231.key root.identity parentDecl.id 0 0 (packet true).bindings

abbrev privateAddress := GeneralNominalIdentities.source raw.seed privateKey

theorem actual_key : privateKey ∈
    GeneralNominalVersionedAllocation231.keys (registry true) root.identity (packet true).bindings := by
  apply List.mem_flatMap.mpr
  refine ⟨parentDecl,List.mem_cons_self,?_⟩
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_flatMap.mpr
  exact ⟨0,by decide,List.mem_cons_self⟩

theorem actually_reserved : privateAddress ∈ supplemented.core.erased.current.context.state.reserved := by
  change privateAddress ∈ GeneralNominalVersionedInstallation231.reserved (packet true)
  exact GeneralNominalVersionedAllocation231.reserved_key actual_key

theorem actual_listed : privateAddress ∈ GeneralNominalState.sources supplemented.core.erased.current.context.state := by
  apply List.mem_append_left
  exact List.mem_append_right _ actually_reserved

theorem private_address_high : 2 < privateAddress := by
  exact GeneralNominalIdentities.source_above_seed raw.seed privateKey

theorem listed_not_recognizable {context : GeneralNominalCandidates.Context}
    (cert : Refresh supplemented context) :
    privateAddress ∈ GeneralNominalState.sources supplemented.core.erased.current.context.state ∧
    ¬ GeneralNominalState.Known context.state privateAddress :=
  ⟨actual_listed,GeneralRebaseRowLedgerFirst288.cannot_certify_private cert _ private_address_high⟩

theorem not_all_listed_public :
    ¬ ∀ n ∈ GeneralNominalState.sources supplemented.core.erased.current.context.state, n ≤ 2 :=
  fun all => (Nat.not_le_of_lt private_address_high) (all _ actual_listed)

end Yulang.GeneralRebaseRowLedgerNames288
