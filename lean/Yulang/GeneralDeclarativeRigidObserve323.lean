import Yulang.GeneralDeclarativeRigidSource323
import Yulang.GeneralDeclarativeDerivedNominal322

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeRigidObserve323
open GeneralDeclarativeHead320 (State Equation environment)
open GeneralDeclarativeDemand320 (Bounds bounds_sound)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeEntailment320 (Entails literal)
open GeneralDeclarativeEqualities322 (Derives entails)
open GeneralDeclarativeRepeatedActual323 (Rigid RigidMany)
open GeneralDeclarativeRigidSource323 (Scanned)
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralNominalCenteredHeadWFSource (PatternCovered)
open GeneralNominalCenteredHeadMatExpressions (translate translate_complete value values)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open GeneralNominalIntervalLaws (nominal_sandwich)
open CommonNominalFullCarrier (subtype_trans)

theorem from_expression {s : State} {p : Pattern} (bounds : Bounds s arg)
    (metadata : PatternCovered c interp p)
    (normal : translate c interp (normalize p) = some code)
    (view : Rigid .actual term code seen)
    (ordinary : Entails s ⟨arg.center,term⟩) :
    Scanned s c interp arg p seen := by
  obtain ⟨raw,spelling⟩ := translate_complete metadata
  exact ⟨⟨term,raw,code,ordinary,spelling,normal,view⟩,bounds⟩

/-- The lower structural source can be an ordinary deduction over
available support, not a literal row. Invariant sandwich uses the upper
ordinary shape to prove the actual center but not to authorize probing. -/
theorem from_invariant {s : State} {support : Supported s completed} {p : Pattern}
    (bounds : Bounds s arg) (metadata : PatternCovered c interp p)
    (normal : translate c interp (normalize p) = some (.nominal tag code))
    (walk : RigidMany .actual lhs code seen)
    (lower : Derives (restriction support) (.variable arg.lower) (.nominal tag lhs))
    (upper : Entails s ⟨arg.upper,.nominal ub rhs⟩) :
    Scanned s c interp arg p seen := by
  apply from_expression bounds metadata normal (.nominal walk)
  intro m valid
  have lo := entails lower m (GeneralDeclarativeOrigins321.restrict_models support m valid)
  have hi := upper m valid
  have inRange := bounds_sound bounds m valid
  exact (nominal_sandwich tag ub
    ((values (environment m) .actual lhs).map Sum.inl)
    ((values (environment m) .actual rhs).map Sum.inl) _
    (subtype_trans lo.2 inRange.1) (subtype_trans inRange.2 hi.1)).1

end Yulang.GeneralDeclarativeRigidObserve323
