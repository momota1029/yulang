import Yulang.GeneralRebaseLeafReceipt288

/-! Concrete separated receipt after every permitted guarded refresh.
It cannot be used to reassert the stronger whole-snapshot property. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29500
set_option maxHeartbeats 19000000
namespace Yulang.GeneralRebaseRowLeafReceipt288
open GeneralRebaseRowChildSource287
open GeneralRebaseRowParentPacket287 (child)
open GeneralRebaseRowLedger288 (supplemented)
open GeneralRebaseRowLeafLifetime288 (source_survives no_fresh_leaf)
open GeneralRebaseRowLeafLocality288 (no_live_requests same_leaf_local_checks)
open GeneralRebaseRowLeafSourceHeads288 (inputObservation actual_head source_supported nested_reads_empty)
open GeneralRebaseRowRefreshPackets288 (child_frame child_transported)
open GeneralRebaseRowRefreshEvidence288 (child_children)
open GeneralRebaseRowRefreshDiagnostics288 (safe merged_clear unique_from_role)
open GeneralRebaseNonleafCommitted276 (result)
open GeneralNominalVersionedMixedObservations233 (Refresh)
open GeneralNominalVersionedRefresh232 (refresh)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalCommonBridge (Assignment)
open GeneralRebaseLeafReceipt288 (Receipt)
open GeneralNominalState (Known)
open GeneralNominalVersionedEvidence231 (Evidence)

variable {context : GeneralNominalCandidates.Context}

theorem receipt (cert : Refresh supplemented context) :
    Receipt (registry true) (refresh supplemented context) (child true) 1 (result child_frame cert) := by
  have unique := unique_from_role cert (.inr rfl) (child_transported cert)
    (GeneralRebaseRowLocal287.child_at_role true)
  rw [child_children cert] at unique
  refine ⟨child_transported cert,safe cert (.inr rfl),merged_clear cert _,unique,child_children cert,
    no_live_requests cert,⟨_,source_survives (context := context)⟩,?_,?_,same_leaf_local_checks cert⟩
  · intro slot
    change ∃ test obs, GeneralNominalSupport.Head context.state 0 test obs ∧ _
    exact ⟨.nominal 6 1,inputObservation cert,actual_head cert,source_supported cert⟩
  · intro slot seen
    change slot ∈ GeneralNominalSupport.readsMany context.state
      (GeneralNominalInspection.queries context.state context.interpretation opaqueChild)
      (result child_frame cert).packet.bounds at seen
    rw [nested_reads_empty cert] at seen
    cases seen

theorem strong_and_weak_separate (cert : Refresh supplemented context) (known : Known context.state 2) :
    Receipt (registry true) (refresh supplemented context) (child true) 1 (result child_frame cert) ∧
    (∀ key p, ¬ GeneralRebaseInertLeaf288.Leaf (registry true) (refresh supplemented context) (child true) key p) ∧
    (∀ m, Models (refresh supplemented context) m →
      Evidence (registry true) (refresh supplemented context).core m (child true) (.node 1 [])) :=
  ⟨receipt cert,no_fresh_leaf cert known (child true),GeneralRebaseLeafReceipt288.instantiate (receipt cert)⟩

theorem no_foreign_receipt (key : Nat) (p : GeneralNominalCenters.Plan roles) :
    ¬ Receipt (registry false) GeneralRebaseForeignLeaf288.unscoped (child false) key p :=
  fun h => GeneralRebaseForeignLeaf288.no_correct_frame key p h.frame

theorem no_pre_emission_receipt (choice : Bool) (key : Nat) (p : GeneralNominalCenters.Plan roles) :
    ¬ Receipt (registry choice) before (child choice) key p :=
  fun h => GeneralRebaseRowLeafWindow288.not_yet_generated choice key p h.frame

end Yulang.GeneralRebaseRowLeafReceipt288
