import Yulang.GeneralDeclarativeI65I74CapturedStabilityCertificate462
import Yulang.GeneralDeclarativeI65I74StableSourceProtocol461

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.CapturedNormalForm462
open EligibleFieldStart461 WrittenPattern460
open Checker408 (Problem)
open RecordTrail455 (EmptyConstructor checkEmpty check_empty_reads_actual_primitive455)
open RoutedReadyMixed457 (ReportAtField)

def ActualSourceSupports {p : Problem} (a : OriginalAnchor p) : Prop :=
  ∃ key, EmptyConstructor p ⟨key,0,[],[]⟩ ∧
    SupportsStable key a.declaration.head a.clause.arguments

def verifyOriginalStability {p : Problem} (a : OriginalAnchor p) (key : Nat) : Bool :=
  checkEmpty p ⟨key,0,[],[]⟩ && verifiesStable key a.declaration.head a.clause.arguments

theorem actual_source_stability_cert_is_independently_reflected
    {p : Problem} (a : OriginalAnchor p) :
    (∃ k, verifyOriginalStability a k = true) ↔ ActualSourceSupports a := by
  simp only [verifyOriginalStability,Bool.and_eq_true,check_empty_reads_actual_primitive455,
    finite_projected_stability_check_exact,ActualSourceSupports]

def actualCapturedStability (p : Problem) : StableSourceProtocol p where
  Certificate := Nat
  supports := ActualSourceSupports
  stability := fun a ⟨k,_,src⟩ => projection_transfers_original_all_captures k
    a.declaration.head a.clause.arguments src
  verifies := verifyOriginalStability
  exact := actual_source_stability_cert_is_independently_reflected

theorem stable_projection_keeps_all_actual_original_source_fields {p : Problem}
    {a : OriginalAnchor p} (start : StartShell p a) (supported : ActualSourceSupports a) :
    ∃ k, readStableShell (actualCapturedStability p) ⟨a.location,k⟩ =
      some (joinActualStable start ((actualCapturedStability p).stability a supported)) := by
  obtain ⟨k,pass⟩ := (actual_source_stability_cert_is_independently_reflected a).mpr supported
  have good : (actualCapturedStability p).verifies a k = true := pass
  refine ⟨k,?_⟩
  simp [readStableShell,actual_finite_shell_replays_without_any_stability_claim a start,
    Option.bind,good]

theorem finite_positive_source_protocol_joins_only_actual_scoped_field_uses
    (p : Problem) (r : ReportAtField) :
    (∃ w, readEligibleField (shellReadyReader (actualCapturedStability p)) w = some r) ↔
      EligibleScoped (shellReadyReader (actualCapturedStability p)) r :=
  finite_stable_shell_and_compiled_path_give_the_exact_same_report _ _

end Yulang.GeneralDeclarativeI65.I72.CapturedNormalForm462
