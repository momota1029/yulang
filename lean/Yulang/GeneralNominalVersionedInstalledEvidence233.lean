import Yulang.GeneralNominalVersionedInstall232
import Yulang.GeneralNominalVersionedTerminal232
import Yulang.GeneralNominalVersionedPreparedTransport231
import Yulang.GeneralNominalVersionedFrameTransport232
import Yulang.GeneralNominalVersionedReplayEffects232
set_option backward.isDefEq.respectTransparency false
/-! Current replayed certificates after an actual versioned installation.
All packet constraints are read from the installed Models judgment. No old
certificate or desired evidence conclusion is assumed. Terminal installation
suffices for transporting the pre-install readiness through request equality. -/
namespace Yulang.GeneralNominalVersionedInstalledEvidence233
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 GeneralNominalVersionedInstall232
open GeneralNominalVersionedInstallation231
open GeneralNominalVersionedEvidence231
open GeneralNominalCommonBridge (Assignment)
variable {roles : Roles.RoleDecls} {state : State roles} {effect : Effect roles} {model : Assignment}

 theorem plan_holds (valid : Models (install state effect) model) :
    GeneralNominalVersionedPlans231.Holds effect.plan model :=
  valid.2.1 effect.plan (List.mem_cons_self ..)

theorem replay_holds (valid : Models (install state effect) model) :
    GeneralNominalVersionedPlans231.Holds (replayPlan effect.plan) model :=
  replay_valid effect.plan model (plan_holds valid)

theorem frame (snapshot : effect.snapshot = state.core) (valid : Models (install state effect) model) :
    Frame effect.registry (install state effect).core effect.plan.packet.site.occurrence
      effect.plan.packet.declaration.id (replayPlan effect.plan) := by
  have original : Frame effect.registry state.core effect.plan.packet.site.occurrence
      effect.plan.packet.declaration.id effect.plan := snapshot ▸ effect.frame
  have reconstructed := GeneralNominalVersionedPreparedTransport231.frame_extended
    (reserved effect.plan.packet) (atoms effect.plan.packet) (allocated effect.plan.packet)
    effect.registry state.core effect.plan.packet.site.occurrence effect.plan.packet.declaration.id effect.plan original
    (by intro key h; unfold allocated; rw [original.registry_eq]; exact h) model (replay_holds valid)
  apply GeneralNominalVersionedFrameTransport232.frame_forward
    (before := GeneralNominalCenteredSteps.refresh state.core
      (GeneralDictionaryOrdinaryTransport.extend state.core.erased.current.context
        (reserved effect.plan.packet) (atoms effect.plan.packet) (allocated effect.plan.packet)))
    (frame := reconstructed)
  · change GeneralDictionaryOrdinaryTransport.extend state.core.erased.current.context _ _ _ =
      GeneralDictionaryOrdinaryTransport.extend effect.plan.packet.context _ _ _
    rw [original.context_eq]
  · intro site member
    exact List.mem_append_left _ member
  · intro site member
    exact List.mem_append_left _ member

theorem class_effects (valid : Models (install state effect) model) :
    GeneralNominalVersionedEffects231.ClassEffects (install state effect).core
      effect.plan.packet.site.occurrence (replayPlan effect.plan) model := by
  apply (GeneralNominalVersionedReplayEffects232.replay_class_effects_iff ..).mpr
  exact (valid.2.2 effect (List.mem_cons_self ..)).2

theorem ready (snapshot : effect.snapshot = state.core)
    (terminal : GeneralNominalVersionedFrame231.children effect.plan.packet = []) :
    GeneralNominalCenteredHeadMatEffects.Ready (install state effect).core
      effect.plan.packet.site.occurrence (replayPlan effect.plan) := by
  apply (GeneralNominalVersionedReplayEffects232.replay_ready_iff ..).mpr
  apply (GeneralNominalVersionedFrameTransport232.ready_iff
    (before := state.core) (after := (install state effect).core)
    (fun _ => (GeneralNominalVersionedTerminal232.requests_iff terminal).symm)).mp
  exact snapshot ▸ effect.ready

theorem certificate (snapshot : effect.snapshot = state.core)
    (terminal : GeneralNominalVersionedFrame231.children effect.plan.packet = [])
    (valid : Models (install state effect) model) :
    Certificate effect.registry (install state effect).core model effect.plan.packet.site.occurrence
      effect.plan.packet.declaration.id [] (replayPlan effect.plan) :=
  certificate_of_semantics (frame snapshot valid)
    ((replay_children effect.plan).trans terminal).symm
    (replay_holds valid) (ready snapshot terminal) (class_effects valid)

theorem evidence (snapshot : effect.snapshot = state.core)
    (terminal : GeneralNominalVersionedFrame231.children effect.plan.packet = [])
    (valid : Models (install state effect) model) :
    Evidence effect.registry (install state effect).core model effect.plan.packet.site.occurrence
      (.node effect.plan.packet.declaration.id []) :=
  evidence_leaf ⟨replayPlan effect.plan,certificate snapshot terminal valid⟩

end Yulang.GeneralNominalVersionedInstalledEvidence233
