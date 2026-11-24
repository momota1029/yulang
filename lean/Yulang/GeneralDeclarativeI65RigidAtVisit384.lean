import Yulang.GeneralDeclarativeI65VisitedUnaryOrdinary384

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65

open GeneralDeclarations (Declaration)
open GeneralDeclarativeK2Graph321 (Shape)
open GeneralDeclarativeGraphRows321 (observed structural)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeInspect321 (Visit PatternK2)
open GeneralNominalCenteredHeadMatExpressions (Expr)

inductive NominalClash384 : Expr → Shape → Prop where
  | label {children : List Nat} : expected ≠ actual →
      NominalClash384 (.nominal expected args) (.nominal actual children)
  | arity {children : List Nat} : args.length ≠ children.length →
      NominalClash384 (.nominal tag args) (.nominal tag children)

/-- A rigid syntactic conflict rules out the identical literal nominal
dispatch shape. It does not rule out a different, separately supported
observation or assert that normalized heads are globally functional. -/
theorem nominal_clash_disagrees_with_literal_dispatch384
    {expected : Nat} {args : List Expr} {actual : Shape}
    (mismatch : NominalClash384 (.nominal expected args) actual) :
    ¬ ∃ children, actual = .nominal expected children ∧ args.length = children.length := by
  rintro ⟨children,eq,len⟩
  subst actual
  cases mismatch with
  | label different => exact different rfl
  | arity different => exact different len

inductive LocalVisitResult384 where
  | k2
  | rigid

/-- Local K2 is checked against the unfiltered graph at an entered
site, even if a known literal mismatch is already available.
The rigid branch needs a positive structural observation, not
failure to construct a successful read/witness. This is not a whole
candidate verdict and neither branch assigns a meaning to absence. -/
inductive UnaryVisitFinding384 (view : Nat → Shape → Prop) (s : State)
    (site : Nat) (query : Expr) : LocalVisitResult384 → Prop where
  | k2 : AliasCycle s.current.ordinary (observed s.current.ordinary) site →
      UnaryVisitFinding384 view s site query .k2
  | rigid :
      ¬AliasCycle s.current.ordinary (observed s.current.ordinary) site →
      view site actual →
      NominalClash384 query actual →
      UnaryVisitFinding384 view s site query .rigid

theorem actual_visit_k2_precedes_positive_clash384
    {view s site query verdict}
    (cycle : AliasCycle s.current.ordinary (observed s.current.ordinary) site)
    (found : UnaryVisitFinding384 view s site query verdict) :
    verdict = .k2 := by
  cases found with
  | k2 => rfl
  | rigid no _ _ => exact (no cycle).elim

/-- A literal selected site in the unary ordinary fragment yields
either original-graph K2 or a positive nominal mismatch in the
current ordinary data. No fitted model is used to produce either. -/
theorem visible_unary_finding_is_sourced384
    {source ordinary tagged direct intervalOrigin constraintOrigin s needs q row root query site inner verdict}
    (literal : UnaryOrdinaryRoot384 direct intervalOrigin constraintOrigin s needs q row root query)
    (supports : ExactSupportForest384 source ordinary tagged s needs)
    (trace : UnaryOrdinaryPrefix384
      (OrdinaryOpenView384 direct intervalOrigin constraintOrigin s needs) s root query site inner)
    (found : UnaryVisitFinding384
      (OrdinaryOpenView384 direct intervalOrigin constraintOrigin s needs) s site inner verdict) :
    row ∈ visible s q ∧ Visit (structural s.current.ordinary) root query site ∧
      match verdict with
      | .k2 => PatternK2 s.current.ordinary root query
      | .rigid => ∃ actual, structural s.current.ordinary site actual ∧ NominalClash384 inner actual := by
  have seen := unary_ordinary_prefix_is_current_visit384 supports trace
  refine ⟨literal.inScope,seen,?_⟩
  cases found with
  | k2 cycle => exact ⟨site,seen,cycle⟩
  | rigid _ observedAt clash =>
    exact ⟨_,close_open_observation384 supports observedAt,clash⟩

end Yulang.GeneralDeclarativeI65
