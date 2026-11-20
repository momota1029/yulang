import Yulang.GeneralRebaseRowLocal287

/-! A whole-type child's direct dictionary certificate need not put a
producer in the recorded plan ledger. The current output-trust rule uses
the latter, not semantic Committed. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 14500000
namespace Yulang.GeneralRebaseRowSettlement287
open GeneralRebaseRowChildSource287
open GeneralRebaseRowParentPacket287 (child childId plan sole_child)
open GeneralRebaseRowParentFrame287 (after effect)
open GeneralNominalVersionedSupport233 (Discharged PacketSettled)
open GeneralNominalSaturationState (Alias)
open GeneralSourceDictionaries (Occurrence)

theorem identities_distinct (choice : Bool) : root.identity ≠ (child choice).identity := by
  have strict : root.identity < childId choice :=
    GeneralNominalIdentities.source_above_invocation raw.seed
      (GeneralNominalAllocation.origin root.identity parentDecl.id 6 requirement.id 0)
  exact Nat.ne_of_lt strict

theorem alias_only_id (choice : Bool) {i j} (alias : Alias (after choice).core.erased.current i j) :
    i = j := by
  induction alias with
  | refl => rfl
  | edge seen => cases seen
  | symm _ ih => exact ih.symm
  | trans _ _ ih jh => exact ih.trans jh

theorem discharged_identity (choice : Bool) {focus : Occurrence roles} (done : Discharged (after choice) focus) :
    focus.identity = root.identity := by
  induction done with
  | packet p present _ _ =>
    change p ∈ [plan choice] at present
    cases List.mem_singleton.mp present
    rfl
  | alias _ _ _ _ related _ ih =>
    exact (alias_only_id choice related).symm.trans ih

theorem no_discharge (choice : Bool) : ¬ Discharged (after choice) (child choice) :=
  fun h => identities_distinct choice (discharged_identity choice h).symm

theorem parent_not_settled (choice : Bool) : ¬ PacketSettled (after choice) (plan choice) := by
  intro h
  exact no_discharge choice (h.2 _ ((sole_child choice).symm ▸ List.mem_singleton_self _))

theorem evidence_without_discharge :
    (∀ m, GeneralNominalVersionedJournal232.Models (after true) m →
      GeneralNominalVersionedEvidence231.Evidence (registry true) (after true).core m (child true) (.node 1 [])) ∧
    GeneralNominalVersionedMixedKernel234.Committed (after true) GeneralRebaseRowWholeChild287.plan ∧
    ¬ Discharged (after true) (child true) :=
  ⟨GeneralRebaseRowWholeChild287.evidence,GeneralRebaseRowWholeChild287.already_committed,no_discharge true⟩

end Yulang.GeneralRebaseRowSettlement287
