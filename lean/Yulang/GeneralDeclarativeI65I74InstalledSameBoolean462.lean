import Yulang.GeneralDeclarativeI65I74OriginalReportProjection462

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.InstalledProtocolSum462
open EligibleFieldStart461
open RetainedFull445 (FullProblem)
open Checker408 (Problem)
open RoutedReadyMixed457 (ReportAtField)
open InlineStructuralPolicy458 (emptyPolicy)

def checkSameField (p : Problem) (i : Provider) (k : Nat)
    (w : AuthenticatedHop458.CycleWire emptyPolicy) (r : ReportAtField) : Bool :=
  decide (dispatchReport (onOldCursor p i k w) = some (r,true))

private theorem same_report_in_option_check {α : Type} (x : Option α)
    (report : α → ReportAtField) (r : ReportAtField) :
    ((x.map fun e => decide (report e = r)).getD false = true) ↔
      x.map report = some r := by
  cases x <;> simp

theorem check_same_field_means_same_report (p : Problem) (i : Provider) (k : Nat)
    (w : AuthenticatedHop458.CycleWire emptyPolicy) (r : ReportAtField) :
    checkSameField p i k w r = true ↔
      ((readActualHeader (provider p i) k).bind fun a => originalField a w) = some r := by
  change decide (dispatchReport (onOldCursor p i k w) = some (r,true)) = true ↔ _
  rw [decide_eq_true_eq]
  exact uniform_reader_on_same_data_matches_original_raw_report p i k w
    (fun _ => all_existing_provider_results_have_original_grammar) r

private theorem exact_bool_of_same_true {x y : Bool} (exact : x = true ↔ y = true) : x = y := by
  cases x <;> cases y <;> simp_all

theorem same_plain_field_bool (p : Problem) (r : ReportAtField) (w : RoutedInlineStructural458.FieldWire) :
    RoutedInlineStructural458.checkField p r w = checkSameField p .plain w.emptyKey w.cursor r := by
  apply exact_bool_of_same_true
  rw [check_same_field_means_same_report,← plain_original_report_projection]
  exact same_report_in_option_check _ _ _

theorem same_projected_field_bool (p : Problem) (r : ReportAtField) (w : ProjectedClosedEntry459.FieldWire) :
    ProjectedClosedEntry459.checkField p r w = checkSameField p .projected w.emptyKey w.cursor r := by
  apply exact_bool_of_same_true
  rw [check_same_field_means_same_report,← projected_original_report_projection]
  exact same_report_in_option_check _ _ _

theorem same_homogeneous_field_bool (p : Problem) (r : ReportAtField) (w : HomogeneousClosedEntry459.FieldWire) :
    HomogeneousClosedEntry459.checkField p r w = checkSameField p .homogeneous w.emptyKey w.cursor r := by
  apply exact_bool_of_same_true
  rw [check_same_field_means_same_report,← homogeneous_original_report_projection]
  exact same_report_in_option_check _ _ _

open HomogeneousClosedEntry459 (Report Witness)

/-- A compatibility calculation on the original wire and report types.
This is not installed as another language entry. The deepest old arm
is delegated exactly; all unmatched tag pairs remain false. -/
def factorExisting (p : FullProblem) : Report → Witness → Bool
  | .fieldK2 r, .fieldK2 w => checkSameField p.old .homogeneous w.emptyKey w.cursor r
  | .previous r, .previous w =>
    match r,w with
    | .fieldK2 r, .fieldK2 w => checkSameField p.old .projected w.emptyKey w.cursor r
    | .previous r, .previous w =>
      match r,w with
      | .fieldK2 r, .fieldK2 w => checkSameField p.old .plain w.emptyKey w.cursor r
      | .previous r, .previous w => RoutedInlineVariant458.check_full458 p r w
      | _,_ => false
    | _,_ => false
  | _,_ => false

theorem existing_canonical_bool_is_factored_on_every_original_input
    (p : FullProblem) (r : Report) (w : Witness) :
    HomogeneousClosedEntry459.check_full_homogeneous459 p r w = factorExisting p r w := by
  cases r with
  | fieldK2 r =>
    cases w with
    | previous => rfl
    | fieldK2 w => exact same_homogeneous_field_bool p.old r w
  | previous previousR =>
    cases w with
    | fieldK2 => rfl
    | previous previousW =>
      cases previousR with
      | fieldK2 r =>
        cases previousW with
        | previous => rfl
        | fieldK2 w => exact same_projected_field_bool p.old r w
      | previous innerR =>
        cases previousW with
        | fieldK2 => rfl
        | previous innerW =>
          cases innerR with
          | fieldK2 r =>
            cases innerW with
            | previous => rfl
            | fieldK2 w => exact same_plain_field_bool p.old r w
          | previous innerR =>
            cases innerW with
            | fieldK2 => rfl
            | previous => rfl

theorem same_existing_classification_and_every_same_fit
    (p : FullProblem) (r : Report) (w : Witness) (yes : factorExisting p r w = true) :
    HomogeneousClosedEntry459.ClassifiedAs p r ∧
      ∀ m, I72.FitsFull p.state m → HomogeneousClosedEntry459.ReportEvidence p m r :=
  HomogeneousClosedEntry459.check_full_sound459 p r w
    ((existing_canonical_bool_is_factored_on_every_original_input p r w).trans yes)

end Yulang.GeneralDeclarativeI65.I72.InstalledProtocolSum462
