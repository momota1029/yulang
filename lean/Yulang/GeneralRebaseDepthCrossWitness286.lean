import Yulang.GeneralRebaseDepthCrossAnchor286

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29500
set_option maxHeartbeats 14000000
namespace Yulang.GeneralRebaseDepthCrossWitness286
open GeneralDictionaryOutputDepth252 (roles root registry model plan)
open GeneralRebaseDepthPreAnchor286 (Anchor)
open GeneralRebaseDepthPrePlan286 (Certified Kept)
open GeneralRebaseDepthPreInstall286 (installed_uses_certified installed_check)
open GeneralNominalVersionedJournal232 (State Effect Models)
open GeneralNominalVersionedMixedKernel234 (Installable)
open GeneralNominalVersionedInstall232 (install)
open GeneralNominalVersionedInstallation231 (replayPlan)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalCenters (Plan)
open GeneralNominalRefinements (Refines)
open GeneralRebaseRetarget275 (Observed retarget)
open GeneralRebaseDepthPathEvidence285 (Witness)

def replay_refines (p : Plan roles) :
    Refines p.packet.context.state (replayPlan p).packet.context.state where
  base := (GeneralNominalRefinements.refl p.packet.context.state).base
  heads := (GeneralNominalRefinements.refl p.packet.context.state).heads
  nominals := (GeneralNominalRefinements.refl p.packet.context.state).nominals
  ordinary := fun _ member => List.mem_append_left _ member
  known := fun _ member => member
  reserved := fun _ member => List.mem_append_left _ member
  allocated := fun _ member => List.mem_append_left _ member
  seed := rfl
  constructors := rfl

theorem replay_retarget (p : Plan roles) : retarget p (replay_refines p) = replayPlan p := by
  have bounds : p.packet.bounds.map (GeneralNominalSlotObservation198.bounds (replay_refines p).base.embed) =
      p.packet.bounds := by
    have identity : GeneralNominalSlotObservation198.bounds (replay_refines p).base.embed = id := by
      funext pair
      cases pair
      rfl
    rw [identity,List.map_id]
  rcases p with ⟨⟨reg,c,s,d,check,b⟩,input,inputEq⟩
  simp only [retarget,replayPlan,GeneralNominalVersionedTransport231.extendedPlan,GeneralNominalVersionedTransport231.extendedPacket]
  congr

theorem replay_observed (p : Plan roles) (known : Observed p) : Observed (replayPlan p) :=
  replay_retarget p ▸ GeneralRebaseRetarget275.observed p (replay_refines p) rfl known

theorem witness {s : State roles} (a : Anchor s) (kept : Kept s) {e : Effect roles}
    (allowed : Installable registry s e) (atRoot : e.plan.packet.site.occurrence = root) :
    Witness (install s e) := by
  have v := installed_uses_certified a kept allowed atRoot
  have valid : Models (install s e) model := (installed_check a kept allowed atRoot model).mpr
    GeneralDictionaryOutputDepthInstall252.installed_model
  have frame := GeneralNominalVersionedInstalledEvidence233.frame allowed.snapshot_eq valid
  rw [allowed.registry_eq,atRoot,v.frame.key_eq] at frame
  have ready := GeneralNominalVersionedInstalledEvidence233.ready allowed.snapshot_eq v.leaf
  rw [atRoot] at ready
  exact ⟨replayPlan e.plan,frame,replay_observed _ v.observed,
    GeneralNominalVersionedCommitted232.replay_committed s e,ready,
    (GeneralNominalVersionedInstallation231.replay_children _).trans v.leaf⟩

theorem kept_of_witness {s : State roles} (w : Witness s) :
    GeneralRebaseDepthPathKeep285.Kept s := by
  obtain ⟨p,frame,seen,committed,_,_⟩ := w
  exact ⟨p,GeneralRebaseDepthPathKeep285.of_frame frame,seen,committed⟩

end Yulang.GeneralRebaseDepthCrossWitness286
