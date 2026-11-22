import Yulang.GeneralDeclarativeStoppedHistory341
import Yulang.GeneralDeclarativeStoppedDiagnostic341

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeStoppedPeers341
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedJournal232 (State Effect Models)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary Local local_iff)
open GeneralNominalCenteredHeadAllocEncoding (registry)
open GeneralNominalSaturationState (Alias Generated)
open GeneralNominalVersionedCandidates231 (Prepared Failed)
open GeneralNominalRefinements (Refines)
open GeneralRebaseRetarget275 (Observed retarget)
open GeneralNominalVersionedMixedChoice236 (choice_iff_no_failed)
open GeneralNominalVersionedMixedFrameSelection235 (selected_identifies)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralDeclarativeStoppedSelected340 (FitFrame source_node)
open GeneralDeclarativeStoppedHistory341 (retarget_frame)
open GeneralDeclarativeStoppedRetarget341 (recorded_semantics)

def NoFailedPeer (r : Registry) (s : State roles) (focus : Occurrence roles) : Prop :=
  ∀ prior ∈ s.core.erased.current.packets,
    Alias s.core.erased.current focus.identity prior.site.occurrence.identity →
    ¬ Failed (registry r) s.core.erased.current.context focus prior.declaration

section
variable {roles : Roles.RoleDecls} {r : Registry} {s : State roles} {root : Occurrence roles}
  {saved : Effect roles}
  (ref : Refines saved.plan.packet.context.state s.core.erased.current.context.state)
  (interp : s.core.erased.current.context.interpretation = saved.plan.packet.context.interpretation)
  (observed : Observed saved.plan)

include interp observed in
/-- The observation-preserving retained case has a full packet in
every actual model. The remaining fit condition is *exactly*
reinspection of previous aliased declarations, not one-key-per-role.
Failed peers are evaluated by the already existing raw judgment. -/
theorem fit_iff
    (checked : (boundary roles).Checked r)
    (path : B4TargetV8.Reachable (boundary roles) r root s)
    (recorded : saved ∈ s.effects)
    (current : Local r s saved.plan.packet.site.occurrence (.selected saved.plan.packet.declaration.id kids))
    (valid : Models s m) :
    FitFrame (s := s) saved.plan.packet.site.occurrence (retarget saved.plan ref) ↔
      NoFailedPeer r s saved.plan.packet.site.occurrence := by
  have choice := choice_iff_no_failed (packet := (retarget saved.plan ref).packet) checked path current
  constructor
  · intro h
    exact choice.mp h.compatible
  · intro no
    have packet := recorded_semantics saved.plan ref interp observed path recorded rfl rfl m valid
    exact ⟨choice.mpr no,m,valid,packet.1,packet.2⟩

include interp observed in
/-- Automatically pair historical physical coordinates and a genuine
current selection of that declaration. This theorem yields the current
Frame and fit, with precise remaining independent source premises. -/
theorem current_of_no_failed
    (checked : (boundary roles).Checked r)
    (path : B4TargetV8.Reachable (boundary roles) r root s)
    (recorded : saved ∈ s.effects)
    (seen : Prepared (registry r) s.core.erased.current.context saved.plan.packet.site.occurrence
      saved.plan.packet.declaration)
    (current : Local r s saved.plan.packet.site.occurrence (.selected k kids))
    (valid : Models s m)
    (no : NoFailedPeer r s saved.plan.packet.site.occurrence) :
    GeneralNominalVersionedEvidence231.Frame (registry r) s.core saved.plan.packet.site.occurrence k
      (retarget saved.plan ref) ∧ FitFrame (s := s) saved.plan.packet.site.occurrence (retarget saved.plan ref) := by
  have frame := retarget_frame path recorded ref seen
  have same := (selected_identifies (local_iff.mp current) frame).1
  exact ⟨same ▸ frame,(fit_iff ref interp observed checked path recorded (same.symm ▸ current) valid).mpr no⟩

end
end Yulang.GeneralDeclarativeStoppedPeers341
