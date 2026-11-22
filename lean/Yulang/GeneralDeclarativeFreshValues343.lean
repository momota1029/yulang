import Yulang.GeneralDeclarativeFreshModel343

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 14500
set_option maxHeartbeats 5700000
namespace Yulang.GeneralDeclarativeFreshValues343
open GeneralDeclarativeLogicalChild343 (stage capture protect output value jobs fresh arg built translated)
open GeneralDeclarativeInitialModels343 (first_values)
open GeneralDeclarativeFreshModel343 (kept)
open GeneralDeclarativeHead320 (State Equation Models environment)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeEntailment320 (appendFacts model_append Holds)
open GeneralDeclarativeFreshInputs325 (names_observed names_bounded)
open GeneralDeclarativeClauseOrigins325 (Origin origin_reads)
open GeneralDeclarativeGrowth327 (restrict)
open GeneralDeclarativeClauseBatch327 (make_grows)
open GeneralDeclarativeSubstitution320 (logical)
open GeneralDeclarativeEqualities322 (semantic)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralWherePhysicalCommit319 (final)
open GeneralWhereOriginSingleCells318 (loNow hi)
open GeneralMixedCompoundChildEquality307 (mid)
open GeneralWherePhysicalChildModel319 (ports mid_value)
open GeneralWhereVersionInstall317 (Models)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Equivalent variant)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl eqv_symm eqv_trans variant_congr)
open GeneralStoppedPlacement335 (Meaning)
open GeneralDeclarativeVersionedChildView342 (arg)

theorem present : jobs[0]? = some (some value) := rfl

theorem printed (keep : List Nat) :
    Origin (built keep) (GeneralDeclarativeLogicalChild343.arg keep).lower
      (logical (capture keep) .lower value) ∧
    Origin (built keep) (GeneralDeclarativeLogicalChild343.arg keep).center
      (logical (capture keep) .actual value) ∧
    Origin (built keep) (GeneralDeclarativeLogicalChild343.arg keep).upper
      (logical (capture keep) .upper value) := by
  have ins := names_observed (s := stage keep) (protect := protect keep) (cap := capture keep) present
  change Origin (built keep) (GeneralDeclarativeSparseWhere325.atPosition (fresh keep) jobs 0).lower
      (logical (capture keep) .lower value) ∧
    Origin (built keep) (GeneralDeclarativeSparseWhere325.atPosition (fresh keep) jobs 0).center
      (logical (capture keep) .actual value) ∧
    Origin (built keep) (GeneralDeclarativeSparseWhere325.atPosition (fresh keep) jobs 0).upper
      (logical (capture keep) .upper value) at ins
  rw [show GeneralDeclarativeSparseWhere325.atPosition (fresh keep) jobs 0 =
    GeneralDeclarativeLogicalChild343.arg keep from GeneralDeclarativeLogicalChild343.port_zero keep] at ins
  exact ins

theorem exact_values (keep : List Nat) (n : Assignment) (fit : GeneralDeclarativeHead320.Models (output keep) n) :
    let logicalArg := GeneralDeclarativeLogicalChild343.arg keep
    Equivalent (n logicalArg.lower).1 (variant 0 (n 2).1) ∧
    Equivalent (n logicalArg.center).1 (variant 0 (n 2).1) ∧
    Equivalent (n logicalArg.upper).1 (variant 0 (n 2).1) := by
  have prepared : GeneralDeclarativeHead320.Models (built keep) n := ((model_append n).mp fit).1
  have stateFit : GeneralDeclarativeHead320.Models (stage keep) n :=
    restrict (make_grows (stage keep) (protect keep) (capture keep) jobs) n prepared
  have common := first_values keep n stateFit
  have known := printed keep
  have lower := semantic (origin_reads known.1) n prepared
  have ctr := semantic (origin_reads known.2.1) n prepared
  have high := semantic (origin_reads known.2.2) n prepared
  change Equivalent (n (GeneralDeclarativeLogicalChild343.arg keep).lower).1
    (variant 0 (n (capture keep 0).lower).1) at lower
  change Equivalent (n (GeneralDeclarativeLogicalChild343.arg keep).center).1
    (variant 0 (n (capture keep 0).center).1) at ctr
  change Equivalent (n (GeneralDeclarativeLogicalChild343.arg keep).upper).1
    (variant 0 (n (capture keep 0).upper).1) at high
  rw [common.2.1] at ctr
  exact ⟨eqv_trans lower (variant_congr 0 common.1),ctr,eqv_trans high (variant_congr 0 common.2.2)⟩

/-- Comparing each mode uses its own proven raw observation. No old
lower or reused center is allowed to stand in for another mode. -/
theorem mode_match (n : Assignment) (raw : GeneralWhereVersionInstall317.Models final n)
    (freshModel : GeneralDeclarativeHead320.Models (output kept) n) :
    Meaning n GeneralDeclarativeVersionedChildView342.arg (GeneralDeclarativeLogicalChild343.arg kept) := by
  have values := exact_values kept n freshModel
  have saved := ports n raw
  exact ⟨eqv_trans saved.1 (eqv_symm values.1),
    eqv_trans (mid_value n raw) (eqv_symm values.2.1),
    eqv_trans saved.2 (eqv_symm values.2.2)⟩

end Yulang.GeneralDeclarativeFreshValues343
