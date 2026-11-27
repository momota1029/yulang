import Yulang.GeneralDeclarativeI65I74CapturedSubpattern462
import Yulang.GeneralDeclarativeI65I74AuthenticCapturedStability462
import Yulang.GeneralDeclarativeI65I74ExactStampedEligible462
import Yulang.GeneralDeclarativeI65I74FiniteCaptureBoundary462

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.CapturedSubpattern462
open EligibleFieldStart461 WrittenPattern460
open Checker408 (Problem)
open RetainedFull445 (FullProblem)
open RoutedReadyMixed457 (ReportAtField)
open CapturedNormalForm462 (ActualSourceSupports verifyOriginalStability
  actual_source_stability_cert_is_independently_reflected actualCapturedStability)

inductive StabilityWire where
  | projectedCount (key : Nat)
  | retainedSyntax (path : List Edge)

def StableAuthority {p : Problem} (src : OriginalAnchor p) : Prop :=
  ActualSourceSupports src ∨ ∃ path, StrictOriginalSubtree src.declaration.head src.clause.arguments path

def checkOwnStability {p : Problem} (src : OriginalAnchor p) : StabilityWire → Bool
  | .projectedCount key => verifyOriginalStability src key
  | .retainedSyntax path => checkStrictSubtree src.declaration.head src.clause.arguments path

theorem check_finite_author_stability_iff_independent_fragment {p : Problem}
    (src : OriginalAnchor p) :
    (∃ w, checkOwnStability src w = true) ↔ StableAuthority src := by
  constructor
  · rintro ⟨w,yes⟩
    cases w with
    | projectedCount key =>
      exact .inl ((actual_source_stability_cert_is_independently_reflected src).mp ⟨key,yes⟩)
    | retainedSyntax path =>
      exact .inr ⟨path,(check_strict_subtree_iff_independent_original_scope ..).mp yes⟩
  · intro auth
    rcases auth with projected | ⟨path,retained⟩
    · obtain ⟨key,yes⟩ := (actual_source_stability_cert_is_independently_reflected src).mpr projected
      exact ⟨.projectedCount key,yes⟩
    · exact ⟨.retainedSyntax path,(check_strict_subtree_iff_independent_original_scope ..).mpr retained⟩

def actualFiniteStability (p : Problem) : StableSourceProtocol p where
  Certificate := StabilityWire
  supports := StableAuthority
  stability := by
    rintro a (generalizes | ⟨path,h⟩)
    · exact (actualCapturedStability p).stability a generalizes
    · exact actual_indexed_head_subtree_supplies_exact_clause_stability a
        ((check_strict_subtree_iff_independent_original_scope ..).mpr h)
  verifies := checkOwnStability
  exact := check_finite_author_stability_iff_independent_fragment

theorem eligible_same_field_iff_finite_author_and_unchanged_structural_witness
    (p : Problem) (r : ReportAtField) (stamp : Bool) :
    ExactStampedSource (shellReadyReader (actualFiniteStability p)) r stamp ↔
      ∃ w, readSourceAndFieldStamp (shellReadyReader (actualFiniteStability p)) w = some (r,stamp) :=
  stamped_source_iff_exact_finite_structural_read _ _ _

theorem no_positive_and_negative_at_same_original_source {p : Problem}
    (a : OriginalAnchor p) (proof : StabilityWire) (bad : FiniteCaptureBoundary462.CaptureTable)
    (yes : checkOwnStability a proof = true) :
    FiniteCaptureBoundary462.badCapture a.declaration.head a.clause.arguments bad = false := by
  have support := (check_finite_author_stability_iff_independent_fragment a).mp ⟨proof,yes⟩
  have stable := (actualFiniteStability p).stability a support
  exact (FiniteCaptureBoundary462.stability_is_exactly_universal_over_finite_tables ..).mp stable bad

end Yulang.GeneralDeclarativeI65.I72.CapturedSubpattern462
