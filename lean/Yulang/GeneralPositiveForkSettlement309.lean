import Yulang.GeneralPositiveForkCompiler309
import Yulang.GeneralPositiveForkHalt309
import Yulang.GeneralCommittedReadEvidence309

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 26500
set_option maxHeartbeats 16500000
namespace Yulang.GeneralPositiveForkSettlement309
open GeneralDeclarations (Registry)
open GeneralPositiveForkSource309 (compiled registry root checked)
open GeneralPositiveForkPlan309 (loSite hiSite kids ordered_children)
open GeneralPositiveForkPreinstall309 (effect)
open GeneralPositiveForkInstall309 (after reachable inhabited)
open GeneralPositiveForkNodes309
open GeneralPositiveForkCompiler309 (read decode lookup_row lookup row projected_children faithful root_computed)
open GeneralCommittedReadEvidence309 (CommittedRead)
open GeneralPositiveForkEvidence309 (alias_identity parentPlan payload)
open GeneralPositiveForkLeaf309 (Side site)
open GeneralNominalVersionedSupport233 (Discharged PacketSettled Trusted Fact)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarationExamples (roles)

theorem committed_read : CommittedRead registry after read decode := by
  intro i e hit
  obtain ⟨n,rfl,rfl⟩ := lookup_row i e hit
  rw [GeneralPositiveForkCompiler309.decode_encode,projected_children]
  exact ⟨plan n,current_frame n,child_list n,GeneralPositiveForkHalt309.committed n⟩

theorem certified_via_commitment :
    B4TargetV8.Classify (boundary roles) registry after root (.selected payload) ∧
    ∀ m, Models after m → (boundary roles).Evidence registry after m root payload :=
  GeneralCommittedReadEvidence309.sound ⟨rfl,checked⟩ reachable
    read decode faithful committed_read 2 0 _ root_computed

theorem only_parent_recorded : after.plans = [GeneralPositiveForkPlan309.plan] := rfl

theorem discharge_owner {f : GeneralSourceDictionaries.Occurrence roles} (d : Discharged after f) :
    f.identity = root.identity := by
  induction d with
  | packet p member _ _ =>
    rw [only_parent_recorded] at member
    cases List.mem_singleton.mp member
    rfl
  | alias a b one two same tracked ih => exact (alias_identity same).symm.trans ih

theorem unrecorded_side (side : Side) : ¬ Discharged after (site side).occurrence :=
  fun d => GeneralPositiveForkLeafFrame309.invocations side (discharge_owner d)

theorem not_settled : ¬ PacketSettled after effect.plan := by
  intro done
  exact unrecorded_side .low (done.2 _ (ordered_children ▸ List.mem_cons_self))

theorem no_trusted_output (facts : List (Fact roles)) (verified : Trusted after facts) :
    Fact.output effect ∉ facts :=
  GeneralNominalVersionedSupport233.no_unsettled_output verified
    (ordered_children ▸ List.mem_cons_self) (unrecorded_side .low)

theorem sound_without_settlement (m : Assignment) (valid : Models after m) :
    GeneralDictionaryDefaultEvidence204.OutputWitness parentPlan m ⟨0,1⟩ ∧
    (boundary roles).Evidence registry after m root payload ∧
    ¬ Discharged after loSite.occurrence ∧ ¬ Discharged after hiSite.occurrence ∧
    ∀ facts, Trusted after facts → Fact.output effect ∉ facts :=
  ⟨GeneralPositiveForkEvidence309.output m valid,certified_via_commitment.2 m valid,
    unrecorded_side .low,unrecorded_side .high,no_trusted_output⟩

end Yulang.GeneralPositiveForkSettlement309
