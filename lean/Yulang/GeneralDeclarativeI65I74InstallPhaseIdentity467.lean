import Yulang.GeneralDeclarativeI65I74NativeProducerInstall465

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.InstallPhaseIdentity467
open Yulang.GeneralDeclarativeI65
open GeneralDeclarativeI65.I72.NativeProducer465
open GeneralDeclarativeWitnessNativePreparation360 (Prepared)
open GeneralDeclarativeWitnessNativeValue360 (Compiled compile)
open GeneralDeclarativeWitnessNativeInstall360 (Board World Committed install current interpreted)
open GeneralDeclarativeWitnessNativeRelease360 (ReleaseAuthority ExactRelease)
open GeneralDeclarativeWitnessAssociatedDescriptor359 (Wire)
open GeneralDeclarativeHead320 (Models)
open GeneralNominalCommonBridge (Assignment)

theorem exact_installed_origin_checks_the_actual_returned_ordinary
    {s : GeneralDeclarativeI65.State} {frame d l}
    {p : Prepared s.current.environment frame d l} {base : Board} {gate : ReleaseAuthority}
    {w : Wire} {version logical ordinal : Nat}
    (strict : checkProducedOrigin p base gate w version logical ordinal = true) :
    ∃ c : Compiled p s.modes w version, ∃ actual : World,
      install p c base = some actual ∧
      actual.ordinary = p.stage ∧ actual.ordinary = s.current.ordinary ∧
      s.origins[ordinal]? = some (originalOfWrite c.write) ∧
      OriginRoute s (originalOfWrite c.write) logical ∧
      Nonempty (ExactRelease actual.board gate c.write) := by
  obtain ⟨c,committed,same,located,route,opened⟩ :=
    (actual_producer_and_same_phase_placement_iff_finite_data ..).mp strict
  exact ⟨c,current p base c.write,(compiler_install_exactly_commits_given_actual_source c base).mpr
    committed,rfl,same,located,route,opened⟩

theorem every_data_wire_declines_a_different_actual_compiler_phase
    {s : GeneralDeclarativeI65.State} {frame d l}
    (p : Prepared s.current.environment frame d l) (different : p.stage ≠ s.current.ordinary)
    (base : Board) (gate : ReleaseAuthority) (w : Wire) (version logical ordinal : Nat) :
    checkProducedOrigin p base gate w version logical ordinal = false := by
  cases test : checkProducedOrigin p base gate w version logical ordinal
  · rfl
  · obtain ⟨_,_,same,_⟩ := (actual_producer_and_same_phase_placement_iff_finite_data ..).mp test
    exact (different same).elim

theorem real_release_of_current_board_uses_no_fresh_scope_in_a_true_fit
    {s : GeneralDeclarativeI65.State} {frame d l}
    {p : Prepared s.current.environment frame d l} {base : Board} {gate : ReleaseAuthority}
    {w : Wire} {version logical ordinal : Nat}
    (strict : checkProducedOrigin p base gate w version logical ordinal = true) (m : Model)
    (fit : GeneralDeclarativeI65.Fits s m) :
    ∃ c : Compiled p s.modes w version, ∃ actual : World,
      install p c base = some actual ∧
      actual.ordinary = s.current.ordinary ∧
      interpreted actual.board m.assignment w.target = some (c.code.eval m.assignment) ∧
      m.nativeSyntax w.target = some (GeneralDeclarativeWitnessNativeOrder362.node c.code) ∧
      Models l.named m.assignment := by
  obtain ⟨c,actual,made,_,same,orig,_route,_release⟩ :=
    exact_installed_origin_checks_the_actual_returned_ordinary strict
  have nativeFit : GeneralDeclarativeWitnessNativeInstall360.Fits actual m.assignment
      (interpreted actual.board m.assignment) :=
    ⟨same.symm ▸ fit.1.1,fun _ => rfl⟩
  have observation := GeneralDeclarativeWitnessNativeInstall360.actual_installation p c made _ _ nativeFit
  exact ⟨c,actual,made,same,observation.1,fit.2 (originalOfWrite c.write) (List.mem_of_getElem? orig),
    observation.2.1⟩

end Yulang.GeneralDeclarativeI65.I72.InstallPhaseIdentity467
