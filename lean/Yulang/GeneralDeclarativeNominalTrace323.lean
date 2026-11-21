import Yulang.GeneralDeclarativeRigidCode323

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeNominalTrace323
open GeneralDeclarativeHead320 (State Equation environment)
open GeneralDeclarativeEntailment320 (Entails Holds)
open GeneralDeclarativeEqualities322 (Derives entails)
open GeneralDeclarativeOrigins321 (Supported restriction restrict_models)
open GeneralDeclarativeTrace321 (Trace)
open GeneralDeclarativeTraceExpand323 (convert expands)
open GeneralDeclarativeRigidCode323 (Code Codes rigid_of_walk)
open GeneralDeclarativeRigidSource323 (Scanned)
open GeneralDeclarativeRigidObserve323 (from_expression)
open GeneralDeclarativeDemand320 (Bounds bounds_sound)
open GeneralNominalCenteredHeadMatExpressions (Expr translate value values)
open GeneralNominalCenteredHeadWFSource (PatternCovered)
open GeneralDeclarationPatterns (normalize)
open GeneralDeclarativeLowerKnown321 (Alias)
open GeneralDeclarativeAliasMeaning321 (alias_sound)
open GeneralNominalIntervalLaws (nominal_sandwich)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans eqv_symm)
open CommonNominalFullCarrier (Equivalent subtype_trans)

theorem invariant_use_tag {s : State} (seen : Trace s mode n (.nominal tag code) raw) :
    Trace s .actual n (.nominal tag code) raw := by
  cases seen with
  | nominal same origin deeper => exact .nominal same origin deeper

theorem lower_nominal_sits {s : State} (view : Trace s mode n (.nominal tag code) raw) :
    ∃ head, Derives s (.variable n) (.nominal tag head) := by
  cases view with
  | nominal same origin _ =>
    exact ⟨_,.trans (.congruent (.variable same)) (.row origin)⟩

/-- This is the actual lower trace of the endpoint probe, with the
upper ordinary nominal sandwich discharging its attachment to the
center. No actual-address lookup or fresh name was needed. -/
theorem from_lower_trace {s : State} {support : Supported s completed}
    (bounds : Bounds s arg) (cover : PatternCovered c interp p)
    (compiled : translate c interp (normalize p) = some (.nominal tag code))
    (kinds : Codes code)
    (lower : Trace (restriction support) .lower arg.lower (.nominal tag code) raw)
    (upper : Entails s ⟨arg.upper,.nominal hi args⟩) :
    Scanned s c interp arg p (raw.map convert) := by
  obtain ⟨head,known⟩ := lower_nominal_sits lower
  obtain ⟨term,proof,walk⟩ := expands (invariant_use_tag lower)
  apply from_expression bounds cover compiled (rigid_of_walk walk (.nominal kinds))
  intro m valid
  have interval := bounds_sound bounds m valid
  have restrict := restrict_models support m valid
  have lo := entails known m restrict
  have hiEq := upper m valid
  have same : Equivalent (m arg.center).1 (value (environment m) .actual (.nominal tag head)) :=
    (nominal_sandwich tag hi ((values (environment m) .actual head).map Sum.inl)
      ((values (environment m) .actual args).map Sum.inl) _
      (subtype_trans lo.2 interval.1) (subtype_trans interval.2 hiEq.1)).1
  exact eqv_trans same (eqv_trans (eqv_symm lo) (entails proof m restrict))

end Yulang.GeneralDeclarativeNominalTrace323
