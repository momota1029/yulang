import Yulang.GeneralNominalVersionedSelectiveHead237
set_option backward.isDefEq.respectTransparency false
/-! Actual child materialization is invariant under the aggregate-only patch.
This does not assert the child's new interval Fits or invent its center value. -/
namespace Yulang.GeneralNominalVersionedSelectiveChild237
open GeneralNominalCenters GeneralNominalVersionedJournal232
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedMixedSelectiveCompletion236 (extended)
open GeneralNominalCenteredHeadMatSchemas
variable (state : State roles) (plan : Plan roles) (model : Assignment)

theorem other_purpose_kept (root declaration purpose owner position : Nat)
    (notLower : purpose ≠ 0) (notUpper : purpose ≠ 1) :
    extended state plan model (fresh plan.packet.context.state.seed root declaration purpose owner position) =
      model (fresh plan.packet.context.state.seed root declaration purpose owner position) := by
  apply GeneralNominalSelectiveEquationRealization236.outside
  intro entry member equal
  obtain ⟨name,_,_,rfl | rfl⟩ := (GeneralNominalVersionedAggregateRealization236.member_iff ..).mp member
  all_goals
    have fields := (GeneralNominalIdentities.source_identity plan.packet.context.state.seed _ _).mp equal
    have purposes := congrArg (fun origin : GeneralNominalIdentities.Origin => origin.2.2.1) fields
    simp only [GeneralNominalAggregateVersion231.key,GeneralNominalAllocation.origin] at purposes
    omega

theorem emitted_center_kept (clause position : Nat) (pattern : GeneralDeclarationPatterns.Pattern) :
    extended state plan model (GeneralNominalVersionedFrame231.emittedCenter plan clause position pattern) =
      model (GeneralNominalVersionedFrame231.emittedCenter plan clause position pattern) := by
  unfold GeneralNominalVersionedFrame231.emittedCenter
  cases GeneralDeclarationPatterns.normalize pattern
  · exact GeneralNominalVersionedSelectiveActual236.binder_kept state plan model _
  all_goals exact other_purpose_kept state plan model _ _ 9 _ _ (by decide) (by decide)

theorem child_center_kept (clause : GeneralDeclarations.Clause) (valid : clause.Signature roles) (index) :
    extended state plan model ((GeneralNominalVersionedFrame231.childSite plan clause valid).center index) =
      model ((GeneralNominalVersionedFrame231.childSite plan clause valid).center index) :=
  emitted_center_kept state plan model _ _ _

theorem actual_equation_iff (equation : Equation) (actual : equation.mode = .actual)
    (target : extended state plan model equation.target = model equation.target) :
    equation.Holds (GeneralNominalVersionedPlans231.variables plan (extended state plan model)) (extended state plan model) ↔
      equation.Holds (GeneralNominalVersionedPlans231.variables plan model) model := by
  unfold Equation.Holds
  rw [target,actual,GeneralNominalVersionedSelectiveActual236.actual_expression]

theorem generated_actual_iff (catalogue : GeneralDeclarationPatterns.Constructors)
    (interpretation : GeneralNominalInspection.Interpretation) (requests : List GeneralNominalMaterialization.Request)
    (actual : ∀ request ∈ requests, request.mode = .actual)
    (targets : ∀ request ∈ requests, extended state plan model request.target = model request.target) :
    (generated catalogue interpretation requests).Holds (GeneralNominalVersionedPlans231.variables plan (extended state plan model)) (extended state plan model) ↔
      (generated catalogue interpretation requests).Holds (GeneralNominalVersionedPlans231.variables plan model) model := by
  induction requests with
  | nil => simp [generated,Schema.Holds]
  | cons first rest ih =>
    simp only [generated,append_holds]
    apply and_congr
    · cases translated : GeneralNominalCenteredHeadMatExpressions.translate catalogue interpretation first.pattern with
      | none => simp [materialize,translated,Schema.Holds]
      | some expression =>
        simp only [materialize,translated,Schema.Holds,List.mem_singleton,forall_eq]
        exact actual_equation_iff state plan model _ (actual first List.mem_cons_self) (targets first List.mem_cons_self)
    · exact ih (fun request member => actual request (List.mem_cons_of_mem _ member))
        (fun request member => targets request (List.mem_cons_of_mem _ member))

theorem child_schema_iff (clause : GeneralDeclarations.Clause) (valid : clause.Signature roles) :
    (GeneralNominalVersionedPlans231.childSchema plan clause valid).Holds
      (GeneralNominalVersionedPlans231.variables plan (extended state plan model)) (extended state plan model) ↔
    (GeneralNominalVersionedPlans231.childSchema plan clause valid).Holds
      (GeneralNominalVersionedPlans231.variables plan model) model := by
  apply generated_actual_iff
  · intro request member
    obtain ⟨index,rfl⟩ := List.mem_ofFn.mp member
    rfl
  · intro request member
    obtain ⟨index,rfl⟩ := List.mem_ofFn.mp member
    exact child_center_kept state plan model clause valid index
end Yulang.GeneralNominalVersionedSelectiveChild237
