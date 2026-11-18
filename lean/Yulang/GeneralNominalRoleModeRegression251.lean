import Yulang.GeneralNominalRoleReadRegression251
import Yulang.GeneralNominalRoleRequests251
namespace Yulang.GeneralNominalRoleModeRegression251
open Core.PresenceGeneration
open GeneralNominalRoleReadRegression251 (env assignment)
open GeneralNominalRoleEnvironment251
open CommonNominalFullCarrier

def equation : GeneralNominalCenteredHeadMatSchemas.Equation := ⟨3,.actual,.variable 0⟩

theorem positional_default_valid :
 (GeneralNominalRoleEquations251.defaultEquation env [1] equation).Holds assignment :=
 ⟨subtype_refl _,subtype_refl _⟩

theorem named_explicit_invalid :
 ¬ (GeneralNominalRoleEquations251.equation [] env equation).Holds assignment := by
 intro held
 exact width_not_below_exactEmpty held.1

theorem nominal_arguments_actual :
 GeneralNominalRebaseEffectView243.compile (variables [] env) .lower (.nominal 9 [.variable 0]) =
 .nominal 9 [.source (.var 0)] := rfl

theorem output_overrides_lower : variables [7] env .lower 7 = .var 0 := rfl

def unknownRequest : GeneralNominalRoleRequests251.Request := ⟨.app 999 [],.var 3,.actual⟩

theorem unknown_flag (interpretation : GeneralNominalInspection.Interpretation) :
 (GeneralNominalRoleRequests251.compile (fun _ => none) interpretation [] env [unknownRequest]).unknown = true := rfl

theorem unknown_equations_empty (interpretation : GeneralNominalInspection.Interpretation) :
 (GeneralNominalRoleRequests251.compile (fun _ => none) interpretation [] env [unknownRequest]).equations = [] := rfl

theorem unknown_holds_vacuously (interpretation : GeneralNominalInspection.Interpretation) :
 GeneralNominalRoleRequests251.Holds (fun _ => none) interpretation [] (read env assignment) assignment unknownRequest := by
 intro expression impossible
 cases impossible

/-- Empty generated equations cannot be confused with successful translation. -/
theorem unknown_not_known (interpretation : GeneralNominalInspection.Interpretation) :
 ¬ (GeneralNominalRoleRequests251.compile (fun _ => none) interpretation [] env [unknownRequest]).unknown = false := by
 rw [unknown_flag]
 decide
end Yulang.GeneralNominalRoleModeRegression251
