import Yulang.GeneralDeclarativeI65OpenOrdinaryRead384
import Yulang.GeneralDeclarativeInspect321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65

open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralDeclarations (Declaration)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralDeclarativeK2Graph321 (Shape)
open GeneralDeclarativeGraphRows321 (observed structural)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeInspect321 (Inspects Visit PatternK2)

abbrev OrdinaryOpenView384 (direct : DirectEquation383)
    (intervalOrigin constraintOrigin : BoundOrigin384) (s : State) (needs : List OutputNeed384) :=
  OpenObserved384 direct intervalOrigin constraintOrigin s needs

/-- One literal visible candidate and the exact unary lower argument
and written query. Both root safety and a positive supported root
read are retained. The interface does not select this candidate. -/
structure UnaryOrdinaryRoot384 (direct : DirectEquation383)
    (intervalOrigin constraintOrigin : BoundOrigin384) (s : State) (needs : List OutputNeed384)
    (q : Request) (row : Declaration) (root : Nat) (query : Expr) : Prop where
  inScope : row ∈ visible s q
  literal : ∃ arg : Capture, q.demand.arguments = [arg] ∧ root = arg.lower
  translated : ∃ pat : Pattern, row.head = [pat] ∧
    translate (authoredRegistry s.current).constructors
      (interpretation s.current.environment.source.snapshot) (normalize pat) = some query
  ready : ∃ shape, OrdinaryOpenView384 direct intervalOrigin constraintOrigin s needs root shape
  inspects : Inspects query
  safe : ¬RootCycle383 s q

inductive UnaryOrdinaryStep384 (view : Nat → Shape → Prop) (s : State) :
    Nat → Expr → Nat → Expr → Prop where
  | primitive :
      ¬AliasCycle s.current.ordinary (observed s.current.ordinary) atName →
      view atName (.primitive tag [child]) → Inspects query →
      UnaryOrdinaryStep384 view s atName (.primitive tag [query]) child query
  | nominal :
      ¬AliasCycle s.current.ordinary (observed s.current.ordinary) atName →
      view atName (.nominal tag [child]) → Inspects query →
      UnaryOrdinaryStep384 view s atName (.nominal tag [query]) child query
  | variant :
      ¬AliasCycle s.current.ordinary (observed s.current.ordinary) atName →
      view atName (.variant tag child) → Inspects query →
      UnaryOrdinaryStep384 view s atName (.variant tag query) child query

/-- Rest of an actual unary inspection prefix. A descent needs the
successful parent dispatch (same tag and sole literal child), parent
K2 safety, and a nonvariable child to inspect. There is no earlier
sibling in this fragment. A bare capture is not a visit. -/
inductive UnaryOrdinaryPrefix384 (view : Nat → Shape → Prop) (s : State) :
    Nat → Expr → Nat → Expr → Prop where
  | here : Inspects query → UnaryOrdinaryPrefix384 view s site query site query
  | next :
      UnaryOrdinaryStep384 view s start outer child query →
      UnaryOrdinaryPrefix384 view s child query endSite endQuery →
      UnaryOrdinaryPrefix384 view s start outer endSite endQuery

theorem unary_ordinary_prefix_is_current_visit384
    {source ordinary tagged direct intervalOrigin constraintOrigin s needs root outer site inner}
    (supports : ExactSupportForest384 source ordinary tagged s needs)
    (trace : UnaryOrdinaryPrefix384
      (OrdinaryOpenView384 direct intervalOrigin constraintOrigin s needs) s root outer site inner) :
    Visit (structural s.current.ordinary) root outer site := by
  induction trace with
  | here inspect => exact .here inspect
  | next step _ later =>
    cases step with
    | primitive _ seen _ =>
      exact .primitive (i := 0) (close_open_observation384 supports seen) rfl rfl later
    | nominal _ seen _ =>
      exact .nominal (i := 0) (close_open_observation384 supports seen) rfl rfl later
    | variant _ seen _ =>
      exact .variant (close_open_observation384 supports seen) later

/-- A genuine reached site is checked in the original ordinary graph.
Support is needed for the descent, not to retain the cyclic rows. -/
theorem reached_unary_ordinary_cycle_is_pattern_k2384
    {source ordinary tagged direct intervalOrigin constraintOrigin s needs root outer site inner}
    (supports : ExactSupportForest384 source ordinary tagged s needs)
    (trace : UnaryOrdinaryPrefix384
      (OrdinaryOpenView384 direct intervalOrigin constraintOrigin s needs) s root outer site inner)
    (cycle : AliasCycle s.current.ordinary (observed s.current.ordinary) site) :
    PatternK2 s.current.ordinary root outer :=
  ⟨site,unary_ordinary_prefix_is_current_visit384 supports trace,cycle⟩

/-- The same finding at the literal visible candidate and argument in
the scope modeled here, not any port that could be visited. This is a
one-candidate finding; an all-visible verdict remains independent. -/
theorem visible_candidate_unary_k2_site384
    {source ordinary tagged direct intervalOrigin constraintOrigin s needs q row root outer site inner}
    (input : UnaryOrdinaryRoot384 direct intervalOrigin constraintOrigin s needs q row root outer)
    (supports : ExactSupportForest384 source ordinary tagged s needs)
    (trace : UnaryOrdinaryPrefix384
      (OrdinaryOpenView384 direct intervalOrigin constraintOrigin s needs) s root outer site inner)
    (cycle : AliasCycle s.current.ordinary (observed s.current.ordinary) site) :
    row ∈ visible s q ∧
    ∃ arg ∈ q.demand.arguments, root = arg.lower ∧
      ¬RootCycle383 s q ∧ PatternK2 s.current.ordinary arg.lower outer := by
  obtain ⟨arg,actual,rfl⟩ := input.literal
  exact ⟨input.inScope,arg,by simp [actual],rfl,input.safe,
    reached_unary_ordinary_cycle_is_pattern_k2384 supports trace cycle⟩

end Yulang.GeneralDeclarativeI65
