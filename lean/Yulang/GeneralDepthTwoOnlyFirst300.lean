import Yulang.GeneralDepthTwoEarlyShared300

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 34500
set_option maxHeartbeats 14500000
namespace Yulang.GeneralDepthTwoOnlyFirst300
open GeneralGeneratedNestedSource299 (root initial)
open GeneralGeneratedNestedPredictions299 (compiled)
open GeneralDepthTwoFirstInstall300 (after)
open GeneralDepthTwoRootFrame300 (frame effect wrong_not_prepared)
open GeneralDepthTwoRootPlan300 (plan)
open GeneralDepthTwoEarlyShared300
open GeneralNominalVersionedJournal232 (State Effect)
open GeneralNominalVersionedMixedTerminalStable234 (no_refresh)
open GeneralNominalVersionedMixedKernel234 (Step Installable)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalExamples (registry)
open GeneralDeclarationExamples (roles display)
open GeneralSourceDictionaries (Occurrence)

theorem phase_frame {p : GeneralNominalCenters.Plan roles} {key}
    (held : Frame compiled initial.core root key p) : p = plan := by
  apply GeneralRebaseScopedFrame276.same_frame held frame
  · rcases GeneralRebaseCompiledDisplay277.compiled_members held.visible held.role_eq with wrong|right
    · exact False.elim (wrong_not_prepared (wrong ▸ held.prepared))
    · exact right
  · exact List.mem_singleton.mp held.raw_recorded
  · exact List.mem_singleton.mp held.center_recorded

theorem only_effect (candidate : Effect roles) (enabled : Installable compiled initial candidate)
    (here : candidate.plan.packet.site.occurrence = root) : candidate = effect := by
  have got := candidate.frame
  rw [enabled.registry_eq,enabled.snapshot_eq,here] at got
  exact same_effect candidate effect enabled.registry_eq enabled.snapshot_eq (phase_frame got)

theorem generated_initial {d : Occurrence roles}
    (given : GeneralNominalSaturationState.Generated initial.core.erased.current root d) : d = root :=
  GeneralNominalVersionedMixedTerminalStable234.generated_only rfl rfl given

theorem only_step (next : State roles) (given : Step compiled root initial next) : next = after := by
  obtain ⟨focus,generated,op⟩ := given
  have atRoot := generated_initial generated
  cases op with
  | administrative action =>
    cases action with
    | enqueue _ absent => exact False.elim (absent _ (List.mem_singleton_self _) atRoot.symm)
    | refresh ctx cert id tracked unknown known =>
      exact False.elim (no_refresh headless_initial cert tracked unknown known)
    | equate a b first last same novel => exact False.elim (novel (equality_initial a b first last same))
    | reobserve rev _ improves =>
      exact False.elim (GeneralNominalReobservationSteps.pointClosed_no_revision closed_initial rev improves)
  | refresh focus ctx cert id tracked unknown known =>
    exact False.elim (no_refresh headless_initial cert tracked unknown known)
  | install candidate enabled _ =>
    cases only_effect candidate enabled atRoot
    rfl
  | merge first last a b same novel =>
    cases List.mem_singleton.mp a
    cases List.mem_singleton.mp b
    exact False.elim (novel (.refl _))

theorem exact_first (next : State roles) :
    (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Step registry root initial next ↔ next = after :=
  ⟨only_step next,fun h => h.symm ▸ GeneralDepthTwoFirstInstall300.actual⟩

end Yulang.GeneralDepthTwoOnlyFirst300
