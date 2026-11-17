import Yulang.GeneralNominalExpressionIntervals237
import Yulang.GeneralNominalVersionedPlans231
set_option backward.isDefEq.respectTransparency false
/-! Derive a child's interval containment from its actual equation and emitted
endpoint equations. The expression's endpoint-read bounds remain explicit. -/
namespace Yulang.GeneralNominalVersionedChildIntervals237
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredHeadMatExpressions GeneralNominalCenteredHeadMatSchemas
open GeneralNominalVersionedPlans231
open CommonNominalFullCarrier
variable {roles : Roles.RoleDecls}

theorem emission_member (plan : Plan roles) (clause : Clause)
    (member : clause ∈ plan.packet.declaration.requirements) (signature : clause.Signature roles) :
    GeneralDeclarationDemands.emit plan.packet.site.occurrence.identity plan.packet.declaration clause signature
      (GeneralNominalVersionedFrame231.capture plan.packet)
      ((GeneralNominalVersionedFrame231.frame plan.packet).allocation plan.packet.declaration.id clause) ∈
    GeneralCanonicalChildOrder.canonicalEmit plan.packet.site.occurrence.identity plan.packet.declaration plan.packet.checked
      (GeneralNominalVersionedFrame231.capture plan.packet)
      ((GeneralNominalVersionedFrame231.frame plan.packet).allocation plan.packet.declaration.id) := by
  apply (GeneralCanonicalChildOrder.canonicalEmit_perm ..).mem_iff.mp
  exact List.mem_map.mpr ⟨⟨clause,member⟩,by simp,rfl⟩

theorem endpoint_requests (plan : Plan roles) (clause : Clause)
    (member : clause ∈ plan.packet.declaration.requirements) (signature : clause.Signature roles)
    (index : Fin (roles clause.role).arity) :
    let pattern := clause.arguments[index.val]'(by rw [signature.1]; exact index.isLt)
    let endpoints := (GeneralNominalVersionedFrame231.childSite plan clause signature).occurrence.demand.arguments index
    (⟨pattern,endpoints.1,.lower⟩ : GeneralNominalMaterialization.Request) ∈ emittedRequests plan.packet ∧
      (⟨pattern,endpoints.2,.upper⟩ : GeneralNominalMaterialization.Request) ∈ emittedRequests plan.packet := by
  have emitted := emission_member plan clause member signature
  constructor
  all_goals
    apply List.mem_append_right
    apply List.mem_flatMap.mpr
    refine ⟨_,emitted,List.mem_append_left _ (List.mem_flatMap.mpr ⟨_,List.mem_ofFn.mpr ⟨index,rfl⟩,?_⟩)⟩
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self

theorem variables_interval (plan : Plan roles) (model : Assignment) (name : Nat)
    (fit : GeneralNominalCaptureMerges.Fits model ((GeneralNominalVersionedFrame231.capture plan.packet).inputs name)
      (model (GeneralNominalVersionedFrame231.binder plan name)).1) :
    Subtype (variables plan model .lower name) (variables plan model .actual name) ∧
      Subtype (variables plan model .actual name) (variables plan model .upper name) := by
  unfold variables
  split
  · exact ⟨subtype_refl _,subtype_refl _⟩
  · exact fit

theorem child_argument_fits (plan : Plan roles) (model : Assignment) (clause : Clause)
    (member : clause ∈ plan.packet.declaration.requirements) (signature : clause.Signature roles)
    (index : Fin (roles clause.role).arity) (expression : Expr)
    (compiled : translate plan.packet.registry.constructors plan.packet.context.interpretation
      (clause.arguments[index.val]'(by rw [signature.1]; exact index.isLt)) = some expression)
    (bounds : ∀ name ∈ GeneralNominalExpressionIntervals237.reads expression,
      GeneralNominalCaptureMerges.Fits model ((GeneralNominalVersionedFrame231.capture plan.packet).inputs name)
        (model (GeneralNominalVersionedFrame231.binder plan name)).1)
    (outputs : Outputs plan model)
    (child : (childSchema plan clause signature).Holds (variables plan model) model) :
    GeneralNominalCaptureMerges.Fits model
      ((GeneralNominalVersionedFrame231.childSite plan clause signature).occurrence.demand.arguments index)
      (model ((GeneralNominalVersionedFrame231.childSite plan clause signature).center index)).1 := by
  have requests := endpoint_requests plan clause member signature index
  have lower := generated_equation outputs requests.1 compiled
  have upper := generated_equation outputs requests.2 compiled
  have actual := generated_equation child (List.mem_ofFn.mpr ⟨index,rfl⟩) compiled
  have interval := GeneralNominalExpressionIntervals237.interval (variables plan model) expression
    (fun name present => variables_interval plan model name (bounds name present))
  exact ⟨subtype_trans lower.1 (subtype_trans interval.1 actual.2),
    subtype_trans actual.1 (subtype_trans interval.2 upper.2)⟩
end Yulang.GeneralNominalVersionedChildIntervals237
