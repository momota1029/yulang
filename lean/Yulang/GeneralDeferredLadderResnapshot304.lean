import Yulang.GeneralDeferredLadderOperationalView304

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeferredLadderResnapshot304
open GeneralDeferredLadderOperationalView304 (View requests_iff classes_iff frame_forward)
open GeneralNominalVersionedJournal232 (State Effect Models)
open GeneralNominalVersionedInstall232 (InstallationModels install install_models)
open GeneralNominalVersionedCycles232 (Safe)
open GeneralNominalVersionedMixedKernel234 (AlternativesSafe)

variable {roles : Roles.RoleDecls} {a b : State roles}

/-- Agreement of the actual context and both views of the occurrence table.
We deliberately compare neither historical effect snapshots nor plan lists. -/
structure HeadView (a b : State roles) : Prop where
  raw : View a b
  context : a.core.erased.current.context = b.core.erased.current.context
  centers : a.core.sites = b.core.sites

theorem HeadView.symm (ab : HeadView a b) : HeadView b a :=
  ⟨ab.raw.symm,ab.context.symm,ab.centers.symm⟩

theorem safe_forward (ab : HeadView a b) (given : Safe a p) : Safe b p := by
  have m : Models a = Models b := funext fun m => propext (ab.raw.models m)
  exact ⟨given.1,fun e he cyclic =>
    given.2 e he ((GeneralNominalVersionedCycles232.full_models_only m).mpr cyclic)⟩

theorem alternatives_forward (ab : HeadView a b) (given : AlternativesSafe registry a input) :
    AlternativesSafe registry b input := by
  intro p exactInput frame
  exact safe_forward ab (given p exactInput (frame_forward ab.raw.symm ab.context.symm ab.centers.symm frame))

theorem ready_forward (ab : HeadView a b)
    (given : GeneralNominalCenteredHeadMatEffects.Ready a.core root p) :
    GeneralNominalCenteredHeadMatEffects.Ready b.core root p := by
  intro output found
  exact given output ((requests_iff ab.raw root output).mpr found)

/-- Rebuild the current effect snapshot with the same plan. This does not
rewrite or assume equality of historical effect snapshots. -/
def resnapshot (ab : HeadView a b) (e : Effect roles) (atA : e.snapshot = a.core) : Effect roles where
  registry := e.registry
  snapshot := b.core
  plan := e.plan
  frame := frame_forward ab.raw ab.context ab.centers (atA ▸ e.frame)
  unique := by
    have same := congrArg (fun c : GeneralNominalCenteredSteps.State roles => c.erased.current.context) atA
    exact (same.trans ab.context) ▸ e.unique
  ready := ready_forward ab (atA ▸ e.ready)

theorem new_effect_iff (ab : HeadView a b) (e : Effect roles)
    (atA : e.snapshot = a.core) (m : GeneralNominalCommonBridge.Assignment) :
    (resnapshot ab e atA).Holds m ↔ e.Holds m := by
  unfold Effect.Holds
  rw [atA]
  exact and_congr_right fun _ => (classes_iff ab.raw e.plan e.plan.packet.site.occurrence m).symm

end Yulang.GeneralDeferredLadderResnapshot304
