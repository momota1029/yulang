import Yulang.GeneralDeclarativeInitialModels343
import Yulang.GeneralDeclarativeOrdinary343

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 15500
set_option maxHeartbeats 6200000
namespace Yulang.GeneralDeclarativeFreshModel343
open GeneralDeclarativeLogicalChild343
  (stage capture protect output child value jobs fresh arg built targets fallback jobs_eq)
open GeneralDeclarativeInitialModels343 (kept_stage first_values first_capture parts)
open GeneralDeclarativeVersionedRootGuard342 (observedRoot every_model)
open GeneralDeclarativeVersionedReceipt342 (ownerOutput current_literals)
open GeneralDeclarativeVersionedChildView342 (code)
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeGrowth327 (Extends restrict)
open GeneralDeclarativeFootprint321 (stateNames)
open GeneralDeclarativeEntailment320 (Holds appendFacts model_append)
open GeneralDeclarativeClauseBatch327 (make_grows)
open GeneralDeclarativeFreshInputs325 (whole_input_projection)
open GeneralDeclarativeClauseOrigins325 (Origin)
open GeneralDeclarativeSubstitution320 (logical)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralWhereOriginSupport318 (journalSources journal_models)
open GeneralWhereVersionInstall317 (Models)
open GeneralWherePhysicalCommit319 (final)
open GeneralWhereOriginSingleSource318 (declaration declaration_checked sourceRegistry)
open GeneralDictionaryJournalRefinement228Source (interpretation)
open GeneralLiveCompoundRegistry316 (otherChild)
open GeneralWhereOriginSingleCells318 (loNow hi)
open GeneralMixedCompoundChildEquality307 (mid)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Equivalent variant)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl eqv_symm eqv_trans variant_congr)

noncomputable abbrev kept := [0,2,4,loNow,mid,hi] ++ journalSources final

theorem names_survive {m n : Assignment} (agree : ∀ k ∈ kept, n k = m k) :
    Models final m ↔ Models final n :=
  journal_models final (fun k present => (agree k (List.mem_append_right _ present)).symm)

theorem cap_bounds (keep : List Nat) : ∀ j ∈ declaration.inputNames, Bounds (stage keep) (capture keep j) := by
  intro j present
  change j ∈ [0,1] at present
  rcases List.mem_cons.mp present with first|rest
  · subst j
    rw [first_capture,parts]
    exact GeneralDeclarativeGrowth327.fits (GeneralDeclarativeOpaqueGroup328.aggregate_grows _ _ _ _)
      (GeneralDeclarativeAggregate324.now_bounds _ _ _ _)
  · cases List.mem_singleton.mp rest
    rw [GeneralDeclarativeInitialModels343.second_capture,parts]
    exact GeneralDeclarativeAggregate324.now_bounds _ _ _ _

theorem built_model (m : Assignment) (fit : Models final m) :
    ∃ n, GeneralDeclarativeHead320.Models (built kept) n ∧
      (∀ k ∈ kept, n k = m k) ∧ Models final n := by
  obtain ⟨u,early,preserved⟩ := kept_stage kept m (every_model m fit)
  have first := whole_input_projection declaration_checked (show otherChild ∈ declaration.requirements from List.mem_cons_self)
    GeneralDeclarativeLogicalChild343.translated (cap_bounds kept) (protect kept) u
  obtain ⟨n,model,agree⟩ := first.mp early
  have stays : ∀ k ∈ kept, n k = m k := fun k h => (agree k
    (List.mem_append_right _ (List.mem_append_right _ h))).trans (preserved k h)
  exact ⟨n,model,stays,(names_survive stays).mp fit⟩

theorem fixed_output_model (m : Assignment) (fit : Models final m) :
    ∃ n, GeneralDeclarativeHead320.Models (output kept) n ∧
      (∀ k ∈ kept, n k = m k) ∧ Models final n := by
  obtain ⟨n,prepared,stays,raw⟩ := built_model m fit
  refine ⟨n,(model_append n).mpr ⟨prepared,?_⟩,stays,raw⟩
  intro row given
  cases List.mem_singleton.mp given
  exact (current_literals n raw).2.1 ownerOutput List.mem_cons_self

end Yulang.GeneralDeclarativeFreshModel343
