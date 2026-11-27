import Yulang.GeneralDeclarativeI65I74InstalledExactScope462
import Yulang.GeneralDeclarativeI65I74PreviousStabilityFactorization461

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.InstalledProtocolSum462
open EligibleFieldStart461 WrittenPattern460
open Checker408 (Problem)
open GeneralDeclarativeWitnessModeCoverage357 (DeclarationCovered)
open RoutedReadyMixed457 (ReportAtField)

private theorem projected_source_has_actual_cover (p : Problem) : CoversActualProducer (alreadyProjected p) :=
  fun _ h => h.preserved.cover

theorem all_actual_providers_cover_exact_selected_declaration (p : Problem) (i : Provider) :
    CoversActualProducer (provider p i) := by
  cases i with
  | plain => exact previousReadyCovers p
  | projected => exact projected_source_has_actual_cover p
  | homogeneous => exact previousHomogeneousCovers p

def installedStabilitySupports {p : Problem} (a : OriginalAnchor p) : Prop :=
  ∃ i : Provider, priorStableAuthority (provider p i) a

def verifyInstalledStability {p : Problem} (a : OriginalAnchor p) (t : Ticket) : Bool :=
  priorVerifyStable (provider p t.author) a t.key

theorem verify_installed_stability_against_original_address {p : Problem} (a : OriginalAnchor p) :
    (∃ t : Ticket, verifyInstalledStability a t = true) ↔ installedStabilitySupports a := by
  constructor
  · rintro ⟨⟨i,k⟩,yes⟩
    exact ⟨i,(prior_replays_same_original_stable_authority (provider p i) a).mp ⟨k,yes⟩⟩
  · rintro ⟨i,auth⟩
    obtain ⟨k,yes⟩ := (prior_replays_same_original_stable_authority (provider p i) a).mpr auth
    exact ⟨⟨i,k⟩,yes⟩

def installedStability (p : Problem) : StableSourceProtocol p :=
  ⟨Ticket,installedStabilitySupports,fun a ⟨i,auth⟩ => (previousStabilityProtocol (provider p i)).stability a auth,
    verifyInstalledStability,verify_installed_stability_against_original_address⟩

theorem separating_finite_original_shell_keeps_exact_installed_header_option
    {p : Problem} (t : Ticket) :
    readStableShell (installedStability p) ⟨⟨0,0,0⟩,t⟩ = pickHeader p t := by
  rcases t with ⟨i,k⟩
  exact each_previous_header_read_factors_through_same_stable_shell _
    (all_actual_providers_cover_exact_selected_declaration p i) k

def splitSourceWire {p : Problem} (w : InstalledWire p) : EligibleWire (shellReadyReader (installedStability p)) :=
  ⟨⟨⟨0,0,0⟩,w.start⟩,w.along⟩

theorem separating_finite_shell_keeps_exact_report_option_and_inherited_stamp
    {p : Problem} (w : InstalledWire p) :
    readSourceAndFieldStamp (shellReadyReader (installedStability p)) (splitSourceWire w) = dispatchReport w := by
  simp only [readSourceAndFieldStamp,dispatchReport,splitSourceWire,shellReadyReader,installedRead,
    separating_finite_original_shell_keeps_exact_installed_header_option]

end Yulang.GeneralDeclarativeI65.I72.InstalledProtocolSum462
