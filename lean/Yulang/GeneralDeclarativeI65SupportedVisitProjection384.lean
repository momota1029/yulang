import Yulang.GeneralDeclarativeI65VisitedUnaryOrdinary384
import Yulang.GeneralDeclarativeI65OrdinarySupportGraph383

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65

open GeneralDeclarativeK2Graph321 (Shape)
open GeneralDeclarativeGraphRows321 (shapeOf structural)
open GeneralDeclarativeInspect321 (Visit)
open GeneralDeclarativeLowerKnown321 (Tag constructorTag)

theorem open_alias_projects_supported_view384
    {source ordinary tagged direct intervalOrigin constraintOrigin s needs a b}
    (supports : ExactSupportForest384 source ordinary tagged s needs)
    (path : OpenAlias384 direct intervalOrigin constraintOrigin s needs a b) :
    LogicalAlias383 (ForgetExactRule384 source) direct ordinary s a b := by
  induction path with
  | bounds lo hi => exact .bounds (open_bound_is_current384 lo) (open_bound_is_current384 hi)
  | forward step => exact .forward (close_open_ordinary_read384 supports step)
  | backward step => exact .backward (close_open_ordinary_read384 supports step)
  | trans _ _ l r => exact .trans l r

theorem open_observation_projects_supported_view384
    {source ordinary tagged direct intervalOrigin constraintOrigin s needs name shape}
    (supports : ExactSupportForest384 source ordinary tagged s needs)
    (read : OpenObserved384 direct intervalOrigin constraintOrigin s needs name shape) :
    structural (finiteOrdinaryView383 (ForgetExactRule384 source) direct ordinary s) name shape := by
  cases read with
  | shape path evidence code =>
    exact ⟨_,logical_alias_matches_supported_ordinary383.mp
      (open_alias_projects_supported_view384 supports path),_,
      finite_ordinary_row_exact383.mpr (close_open_ordinary_read384 supports evidence),code⟩

/-- Every descent of the scoped inspection is still a visit in
the supported view. This is independent of the larger graph
against which K2 is tested at reached sites. -/
theorem unary_prefix_visits_in_supported_view384
    {source ordinary tagged direct intervalOrigin constraintOrigin s needs root outer site inner}
    (supports : ExactSupportForest384 source ordinary tagged s needs)
    (trace : UnaryOrdinaryPrefix384
      (OrdinaryOpenView384 direct intervalOrigin constraintOrigin s needs) s root outer site inner) :
    Visit (structural (finiteOrdinaryView383 (ForgetExactRule384 source) direct ordinary s))
      root outer site := by
  induction trace with
  | here now => exact .here now
  | next step _ rest =>
    cases step with
    | primitive _ seen _ =>
      exact .primitive (i := 0) (open_observation_projects_supported_view384 supports seen) rfl rfl rest
    | nominal _ seen _ =>
      exact .nominal (i := 0) (open_observation_projects_supported_view384 supports seen) rfl rfl rest
    | variant _ seen _ =>
      exact .variant (open_observation_projects_supported_view384 supports seen) rest

theorem normalized_structural_shape_exposes_a_tag384
    {exp : GeneralNominalCenteredHeadMatExpressions.Expr} {shape : Shape}
    (normalized : shapeOf exp = some shape) :
    ∃ tag : Tag, constructorTag exp = some tag := by
  cases exp with
  | «variable» _ => cases normalized
  | join _ _ => cases normalized
  | primitive _ _ => exact ⟨_,rfl⟩
  | nominal _ _ => exact ⟨_,rfl⟩
  | record _ _ _ => exact ⟨_,rfl⟩
  | variant _ _ => exact ⟨_,rfl⟩

theorem open_observed_exposes_supported_lower384
    {source ordinary tagged direct intervalOrigin constraintOrigin s needs name shape}
    (supports : ExactSupportForest384 source ordinary tagged s needs)
    (read : OpenObserved384 direct intervalOrigin constraintOrigin s needs name shape) :
    ∃ tag, LogicalKnows383 (ForgetExactRule384 source) direct ordinary s name tag := by
  cases read with
  | shape path evidence code =>
    obtain ⟨tag,reveals⟩ := normalized_structural_shape_exposes_a_tag384 code
    exact ⟨tag,_,close_open_ordinary_read384 supports evidence,
      open_alias_projects_supported_view384 supports path,reveals⟩

theorem unary_literal_known_root_projects_inspection_entry384
    {source ordinary tagged direct intervalOrigin constraintOrigin s needs q row root outer}
    (supports : ExactSupportForest384 source ordinary tagged s needs)
    (literal : UnaryOrdinaryRoot384 direct intervalOrigin constraintOrigin s needs q row root outer) :
    RootEntry383 s q (LogicalOrdinaryRootReady383 (ForgetExactRule384 source) direct ordinary s q) .inspect := by
  refine .inspect literal.safe ?_
  obtain ⟨input,atInput,rootAt⟩ := literal.literal
  obtain ⟨shape,found⟩ := literal.ready
  intro arg present
  have same : arg = input := by simpa [atInput] using present
  subst arg
  simpa [rootAt] using open_observed_exposes_supported_lower384 supports found

end Yulang.GeneralDeclarativeI65
