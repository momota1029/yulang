import Yulang.GeneralDeclarativeNestedModels332
import Yulang.GeneralDeclarativeInlineBoundary331

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeNestedClash332
open GeneralDeclarativeHead320 (State Models environment)
open GeneralDeclarativeOrigins321 (Supported restriction restrict_models)
open GeneralDeclarativeEqualities322 (Derives semantic)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeBounds319 (bound_sound)
open GeneralDeclarativeRecordSpine330 (Terminal)
open GeneralDeclarativeRecordResidual323 (withTail)
open GeneralDeclarativeRecordPayloads330 (Field visible has_field)
open GeneralDeclarativeRecordIntervals330 (projected_below)
open GeneralDeclarativeInlineNegative331 (missing_projection)
open GeneralDeclarativeRepeatedActual323 (eqAt)
open GeneralNominalCenteredHeadMatExpressions (Expr value)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Subtype subtype_trans common_pair_iff common_variant_iff)
open CommonRoleCanonicalRows (lookup)

abbrev pairExpr (a b : Expr) := Expr.primitive .pair [a,b]

/-- Proven negative evidence travels through actual covariant
constructor positions and visible required fields. Failure of the
ordinary source reader is not an evidence constructor. -/
inductive Apart : Expr → Expr → Prop where
  | missing : Terminal stop → lookup key raw = none → Field key desiredFields payload →
      Apart (withTail raw stop) (withTail desiredFields wantTail)
  | field : Field key lhs a → Field key rhs b → Apart a b →
      Apart (withTail lhs leftTail) (withTail rhs rightTail)
  | first : Apart a b → Apart (pairExpr a x) (pairExpr b y)
  | second : Apart a b → Apart (pairExpr x a) (pairExpr y b)
  | tagged : Apart a b → Apart (.variant key a) (.variant key b)

theorem sound (negative : Apart raw target) (m : Assignment) :
    ¬Subtype (value (environment m) .actual raw) (value (environment m) .actual target) := by
  induction negative with
  | missing closed absent targetField =>
    intro below
    obtain ⟨_,proof⟩ := has_field (visible targetField _ m) below
    rw [missing_projection _ m _ closed absent] at proof
    cases proof
  | field left right _ ih =>
    intro below
    exact ih (projected_below _ false (visible left _ m) (visible right _ m) below)
  | first _ ih =>
    intro below
    exact ih (((common_pair_iff ..).mp below).1)
  | second _ ih =>
    intro below
    exact ih (((common_pair_iff ..).mp below).2)
  | tagged _ ih =>
    intro below
    exact ih ((common_variant_iff ..).mp below)

/-- A supported lower witness gives a semantic obstruction to the
candidate layout for every current model. The theorem does not turn
an absent upper view or an opaque tail into rejection. -/
theorem from_lower {s : State} {p : Supported s done}
    (box : Bounds s a) (original : Derives (restriction p) (.variable a.lower) raw)
    (negative : Apart raw wanted) (m : Assignment) (valid : Models s m) :
    ¬eqAt m (.variable a.center) wanted := by
  intro would
  have seen := semantic original m (restrict_models p m valid)
  exact sound negative m (subtype_trans seen.2 (subtype_trans (bound_sound m valid.1 box.1) would.1))

end Yulang.GeneralDeclarativeNestedClash332
