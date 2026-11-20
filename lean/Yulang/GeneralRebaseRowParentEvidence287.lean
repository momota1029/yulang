import Yulang.GeneralRebaseRowWholeChild287

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 14500000
namespace Yulang.GeneralRebaseRowParentEvidence287
open GeneralRebaseRowChildSource287
open GeneralRebaseRowParentPacket287
open GeneralRebaseRowParentFrame287
open GeneralRebaseRowGeneratedChild287 (emitted_center)
open GeneralNominalVersionedEvidence231 (Evidence Frame Instance)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedInstallation231 (replayPlan)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenters (Plan)

theorem raw_sites (choice : Bool) : (after choice).core.erased.current.sites =
    [GeneralNominalDemandMerging.pointSite root,(center choice).observed] := by
  change [_] ++ GeneralNominalVersionedChildren232.rawSites (plan choice) = _
  rw [GeneralNominalVersionedChildren232.rawSites,emitted_center]
  rfl

theorem centers (choice : Bool) : (after choice).core.sites =
    [(plan choice).input,center choice] := by
  change [_] ++ GeneralNominalVersionedChildren232.emitted (plan choice) = _
  rw [emitted_center]
  rfl

theorem roles_distinct (choice : Bool) : root.demand.role ≠ (child choice).demand.role := by
  change (0 : Nat) ≠ 1
  decide

theorem replay_frame (choice : Bool) (m : Assignment) (valid : Models (after choice) m) :
    Frame (registry choice) (after choice).core root 0 (replayPlan (plan choice)) :=
  GeneralNominalVersionedInstalledEvidence233.frame (effect := effect choice) rfl valid

theorem requests_ready (choice : Bool) :
    GeneralNominalCenteredHeadMatEffects.Ready (after choice).core root (replayPlan (plan choice)) := by
  apply (GeneralNominalVersionedReplayEffects232.replay_ready_iff ..).mpr
  exact (GeneralNominalVersionedFrameTransport232.ready_iff
    (before := before.core) (after := (after choice).core)
    (fun q => (after_requests choice q).symm)).mp (ready choice)

theorem instance_root (choice : Bool) (m : Assignment) (valid : Models (after choice) m) :
    Instance (registry choice) (after choice).core m root 0 [child choice] := by
  refine ⟨replayPlan (plan choice),GeneralNominalVersionedEvidence231.certificate_of_semantics
    (replay_frame choice m valid) ?_
    (GeneralNominalVersionedInstalledEvidence233.replay_holds (effect := effect choice) valid)
    (requests_ready choice)
    (GeneralNominalVersionedInstalledEvidence233.class_effects (effect := effect choice) valid)⟩
  exact ((GeneralNominalVersionedInstallation231.replay_children _).trans (sole_child choice)).symm

theorem evidence_root (m : Assignment) (valid : Models (after true) m) :
    Evidence (registry true) (after true).core m root (.node 0 [.node 1 []]) :=
  GeneralNominalVersionedEvidence231.evidence_node (instance_root true m valid)
    (.cons (GeneralRebaseRowWholeChild287.evidence m valid) .nil)

theorem only_root_plan (choice : Bool) (m : Assignment) (valid : Models (after choice) m)
    {p : Plan roles} {key} (one : Frame (registry choice) (after choice).core root key p) :
    p = replayPlan (plan choice) := by
  have replay := replay_frame choice m valid
  have sameD := at_role choice _ one.visible one.role_eq
  have site_eq : ∀ s ∈ (after choice).core.erased.current.sites, s.occurrence = root →
      s = GeneralNominalDemandMerging.pointSite root := by
    intro s present atRoot
    rw [raw_sites] at present
    simp only [List.mem_cons,List.not_mem_nil,or_false] at present
    rcases present with rfl|rfl
    · rfl
    · exact (roles_distinct choice (congrArg (fun o : GeneralSourceDictionaries.Occurrence roles => o.demand.role)
        atRoot.symm)).elim
  have center_eq : ∀ s ∈ (after choice).core.sites, s.occurrence = root → s = (plan choice).input := by
    intro s present atRoot
    rw [centers] at present
    simp only [List.mem_cons,List.not_mem_nil,or_false] at present
    rcases present with rfl|rfl
    · rfl
    · exact (roles_distinct choice (congrArg (fun o : GeneralSourceDictionaries.Occurrence roles => o.demand.role)
        atRoot.symm)).elim
  have rawSame := (site_eq _ one.raw_recorded one.occurrence_eq).trans
    (site_eq _ replay.raw_recorded replay.occurrence_eq).symm
  have centerSame := (center_eq _ one.center_recorded (p.input_exact.trans one.occurrence_eq)).trans
    (center_eq _ replay.center_recorded ((replayPlan (plan choice)).input_exact.trans replay.occurrence_eq)).symm
  exact GeneralRebaseScopedFrame276.same_frame one replay sameD rawSame centerSame

end Yulang.GeneralRebaseRowParentEvidence287
