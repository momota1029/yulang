import Yulang.GeneralDepthTwoFinalScope300
import Yulang.GeneralDepthTwoFinalSeparators300

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 34000
set_option maxHeartbeats 14000000
namespace Yulang.GeneralDepthTwoFinalHalt300
open GeneralGeneratedNestedSource299 (root model)
open GeneralGeneratedNestedPredictions299 (compiled middle terminal)
open GeneralDepthTwoSecondInstall300 (final)
open GeneralDepthTwoFinalScope300
open GeneralDepthTwoFinalSeparators300 (headless equality_closed)
open GeneralDepthTwoFinalNodes300
open GeneralNominalVersionedMixedTerminalStable234 (no_refresh)
open GeneralNominalVersionedMixedKernel234 (Step Stable)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalSaturationState (Generated)
open GeneralNominalExamples (registry)
open GeneralDeclarationExamples (roles)
open GeneralSourceDictionaries (Occurrence)

theorem recorded (focus : Occurrence roles) (reachable : Generated final.core.erased.current root focus) :
    ∃ s ∈ final.core.erased.current.sites, s.occurrence = focus := by
  obtain ⟨n,matched⟩ := generated_only focus reachable
  have f := frame n model GeneralDepthTwoTerminalFrame300.final_model
  exact ⟨(plan n).packet.site,f.raw_recorded,f.occurrence_eq.trans matched.symm⟩

theorem halted (next : State roles) : ¬ Step compiled root final next := by
  rintro ⟨focus,generated,op⟩
  cases op with
  | administrative action =>
    cases action with
    | enqueue _ absent =>
      obtain ⟨s,seen,place⟩ := recorded _ generated
      exact absent s seen place
    | refresh context cert id tracked unknown known =>
      exact no_refresh headless cert tracked unknown known
    | equate first last a b same novel =>
      exact novel (equality_closed first last a b same)
    | reobserve rev _ improves =>
      exact GeneralNominalReobservationSteps.pointClosed_no_revision point_closed rev improves
  | refresh focus context cert id tracked unknown known =>
    exact no_refresh headless cert tracked unknown known
  | install candidate enabled novel =>
    exact novel (no_raw_install candidate enabled generated)
  | merge first last a b same novel =>
    obtain ⟨an,eq⟩ := center_hit _ a
    obtain ⟨bn,eq'⟩ := center_hit _ b
    subst first; subst last
    cases centers_equal an bn same
    exact novel (.refl _)

theorem source_halted (next : State roles) : ¬ (boundary roles).Step registry root final next :=
  halted next

theorem stable (n : Node) : (boundary roles).Stable registry final (demand n) := by
  have pair := GeneralNominalVersionedMixedSourceBoundary234.closure source_halted
  cases n
  · exact pair.1
  · exact pair.2 middle (.child .root
      (GeneralDepthTwoEvidence300.final_edges ▸ List.mem_cons_self ..))
  · exact pair.2 terminal GeneralDepthTwoSecondInstall300.actual_terminal.2.2

end Yulang.GeneralDepthTwoFinalHalt300
