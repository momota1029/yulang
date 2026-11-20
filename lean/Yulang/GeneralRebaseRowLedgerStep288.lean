import Yulang.GeneralRebaseRowLedger288
import Yulang.GeneralRebaseRowActualPaths287

/-! Against a hypothetical supplemented ledger, a downstream refresh is
an actual instance of the old Step. The supplementation itself is not. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28500
set_option maxHeartbeats 18000000
namespace Yulang.GeneralRebaseRowLedgerStep288
open GeneralRebaseRowChildSource287
open GeneralRebaseRowParentFrame287 (after)
open GeneralRebaseRowLedger288 (supplemented old_refresh unknown_output models_eq)
open GeneralRebaseRowSemanticMark287 (target known_output)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralNominalVersionedJournal232 (Models State)
open GeneralNominalCommonBridge (Assignment)

noncomputable abbrev refreshed : State roles := GeneralNominalVersionedRefresh232.refresh supplemented (target true)

theorem listed_output : 2 ∈ GeneralNominalState.sources supplemented.core.erased.current.context.state := by
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_append_left
  exact List.mem_ofFn.mpr ⟨(2 : Fin 3),rfl⟩

theorem real_refresh_at_hypothetical_state : Step (registry true) root supplemented refreshed :=
  ⟨root,.root,.refresh root (target true) old_refresh 2 listed_output (unknown_output true) (known_output true)⟩

theorem refreshed_model_eq (m : Assignment) : Models refreshed m ↔ Models (after true) m :=
  (GeneralNominalVersionedMixedObservations233.refresh_models old_refresh).trans (models_eq m)

theorem supplemented_ne_original : supplemented ≠ after true := by
  intro same
  have length := congrArg (fun s : State roles => s.plans.length) same
  change (2 : Nat) = 1 at length
  cases length

theorem supplemented_ne_before : supplemented ≠ before := by
  intro same
  have length := congrArg (fun s : State roles => s.plans.length) same
  change (2 : Nat) = 0 at length
  cases length

theorem no_raw_path_to_supplement :
    ¬ B4Target.Steps (Step (registry true) root) before supplemented := by
  intro trace
  exact (GeneralRebaseRowActualPaths287.one_or_zero true _ trace).elim
    supplemented_ne_before supplemented_ne_original

theorem no_raw_path_from_endpoint :
    ¬ B4Target.Steps (Step (registry true) root) (after true) supplemented := by
  intro trace
  have prepend (s : State roles) (tail : B4Target.Steps (Step (registry true) root) (after true) s) :
      B4Target.Steps (Step (registry true) root) before s := by
    induction tail with
    | refl => exact .tail .refl (GeneralRebaseRowParentStep287.actual_step true)
    | tail _ edge ih => exact .tail ih edge
  exact no_raw_path_to_supplement (prepend _ trace)

theorem no_model_only_enabledness (m : Assignment) :
    (Models supplemented m ↔ Models (after true) m) ∧
    (∀ next, ¬ Step (registry true) root (after true) next) ∧
    Step (registry true) root supplemented refreshed :=
  ⟨models_eq m,GeneralRebaseRowClosure287.no_step true,real_refresh_at_hypothetical_state⟩

end Yulang.GeneralRebaseRowLedgerStep288
