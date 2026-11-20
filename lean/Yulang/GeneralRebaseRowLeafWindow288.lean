import Yulang.GeneralRebaseRowLeafSourceHeads288

/-! The source-only witness is created only after the real child exists.
It is a historical witness: it must not be re-demanded after adding the
already justified parent observation to the full raw packet context. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29000
set_option maxHeartbeats 17000000
namespace Yulang.GeneralRebaseRowLeafWindow288
open GeneralRebaseRowChildSource287
open GeneralRebaseRowParentPacket287 (child)
open GeneralRebaseRowParentFrame287 (after)
open GeneralRebaseRowLedger288 (supplemented)
open GeneralRebaseRowLeafLifetime288 (no_fresh_leaf)
open GeneralRebaseInertLeaf288 (Leaf)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedMixedObservations233 (Refresh)
open GeneralNominalVersionedRefresh232 (refresh)
open GeneralNominalState (Known)
open GeneralNominalCenters (Plan)

theorem not_yet_generated (choice : Bool) (key : Nat) (p : Plan roles) :
    ¬ Frame (registry choice) before.core (child choice) key p := by
  intro localFrame
  have found := localFrame.raw_recorded
  change p.packet.site ∈ [GeneralNominalDemandMerging.pointSite root] at found
  have same := (congrArg GeneralNominalDemandMerging.Site.occurrence (List.mem_singleton.mp found)).symm.trans
    localFrame.occurrence_eq
  exact GeneralRebaseRowParentEvidence287.roles_distinct choice
    (congrArg (fun focus : GeneralSourceDictionaries.Occurrence roles => focus.demand.role) same)

def Present (choice : Bool) (state : State roles) : Prop :=
  ∃ key p, Leaf (registry choice) state (child choice) key p

theorem before_absent (choice : Bool) : ¬ Present choice before := by
  rintro ⟨k,p,cert⟩
  exact not_yet_generated choice k p cert.frame

theorem real_endpoint_iff (choice : Bool) : Present choice (after choice) ↔ choice = true := by
  cases choice
  · constructor
    · rintro ⟨k,p,cert⟩
      exact (GeneralRebaseRowLeafWitness288.no_leaf k p cert).elim
    · intro impossible; cases impossible
  · exact ⟨fun _ => rfl,fun _ => ⟨1,_,GeneralRebaseRowLeafWitness288.leaf⟩⟩

theorem post_mark_absent {context : GeneralNominalCandidates.Context}
    (cert : Refresh supplemented context) (known : Known context.state 2) :
    ¬ Present true (refresh supplemented context) := by
  rintro ⟨k,p,fresh⟩
  exact no_fresh_leaf cert known (child true) k p fresh

theorem actual_activation_window (choice : Bool) :
    ¬ Present choice before ∧ (Present choice (after choice) ↔ choice = true) ∧
    GeneralNominalVersionedMixedKernel234.Step (registry choice) root before (after choice) :=
  ⟨before_absent choice,real_endpoint_iff choice,GeneralRebaseRowParentStep287.actual_step choice⟩

end Yulang.GeneralRebaseRowLeafWindow288
