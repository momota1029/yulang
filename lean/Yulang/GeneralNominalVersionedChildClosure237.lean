import Yulang.GeneralNominalModeIntervals237
import Yulang.GeneralNominalVersionedChildIntervals237
import Yulang.GeneralNominalVersionedCurrentHead237
import Yulang.GeneralNominalVersionedMixedReady235
set_option backward.isDefEq.respectTransparency false
/-! Child interval Fits is a theorem, not an independent model premise: actual
child equations, total emitted outputs and scoped head captures imply it.
Normalized scope handles erased record fields; no lexical scope is added. -/
namespace Yulang.GeneralNominalVersionedChildClosure237
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedPlans231 GeneralNominalCenteredHeadWFSource
open GeneralNominalCenteredHeadMatExpressions GeneralNominalCenteredHeadMatSchemas
open CommonNominalFullCarrier
variable {roles : Roles.RoleDecls}

theorem normalized_argument (patterns : List Pattern) (pattern : Pattern) (member : pattern ∈ patterns) :
    normalize pattern ∈ normalizeArgs patterns := by
  induction patterns with
  | nil => cases member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with rfl | later
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih later)

theorem argument_variables (patterns : List Pattern) (pattern : Pattern) (member : pattern ∈ patterns) :
    pattern.variables ⊆ variablesArgs patterns := by
  induction patterns with
  | nil => cases member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with rfl | later
    · exact fun _ h => List.mem_append_left _ h
    · exact fun _ h => List.mem_append_right _ (ih later h)

theorem child_argument_fits (plan : Plan roles) (model : Assignment) (clause : Clause)
    (member : clause ∈ plan.packet.declaration.requirements) (signature : clause.Signature roles)
    (index : Fin (roles clause.role).arity) (expression : Expr)
    (compiled : translate plan.packet.registry.constructors plan.packet.context.interpretation
      (clause.arguments[index.val]'(by rw [signature.1]; exact index.isLt)) = some expression)
    (captures : ∀ name ∈ plan.packet.declaration.inputNames,
      GeneralNominalCaptureMerges.Fits model ((GeneralNominalVersionedFrame231.capture plan.packet).inputs name)
        (model (GeneralNominalVersionedFrame231.binder plan name)).1)
    (outputs : Outputs plan model)
    (child : (childSchema plan clause signature).Holds (variables plan model) model) :
    GeneralNominalCaptureMerges.Fits model
      ((GeneralNominalVersionedFrame231.childSite plan clause signature).occurrence.demand.arguments index)
      (model ((GeneralNominalVersionedFrame231.childSite plan clause signature).center index)).1 := by
  have requests := GeneralNominalVersionedChildIntervals237.endpoint_requests plan clause member signature index
  have lower := generated_equation outputs requests.1 compiled
  have upper := generated_equation outputs requests.2 compiled
  have actual := generated_equation child (List.mem_ofFn.mpr ⟨index,rfl⟩) compiled
  have interval := GeneralNominalModeIntervals237.compiled_interval (variables := variables plan model) compiled (by
    intro name present
    apply GeneralNominalVersionedChildIntervals237.variables_interval
    apply captures
    apply plan.packet.checked.scope.1 clause member name
    exact argument_variables (normalizeArgs clause.arguments) _
      (normalized_argument clause.arguments _ (List.getElem_mem ..)) present)
  exact ⟨subtype_trans lower.1 (subtype_trans interval.1 actual.2),
    subtype_trans actual.1 (subtype_trans interval.2 upper.2)⟩

theorem child_holds (plan : Plan roles) (model : Assignment)
    (covered : DeclarationCovered plan.packet.registry.constructors plan.packet.context.interpretation plan.packet.declaration)
    (captures : ∀ name ∈ plan.packet.declaration.inputNames,
      GeneralNominalCaptureMerges.Fits model ((GeneralNominalVersionedFrame231.capture plan.packet).inputs name)
        (model (GeneralNominalVersionedFrame231.binder plan name)).1)
    (outputs : Outputs plan model) (clause : Clause)
    (member : clause ∈ plan.packet.declaration.requirements) (signature : clause.Signature roles)
    (child : (childSchema plan clause signature).Holds (variables plan model) model) :
    (GeneralNominalVersionedFrame231.childSite plan clause signature).Holds model := by
  intro index
  obtain ⟨expression,compiled⟩ := translate_complete
    (patterns_member (covered.2.1 clause member).1
      (List.getElem_mem (l := clause.arguments) (n := index.val) (by rw [signature.1]; exact index.isLt)))
  exact child_argument_fits plan model clause member signature index expression compiled captures outputs child

theorem holds_iff (state : GeneralNominalVersionedJournal232.State roles) (plan : Plan roles) (model : Assignment)
    (frame : GeneralNominalVersionedEvidence231.Frame registry state.core focus key plan)
    (covered : DeclarationCovered plan.packet.registry.constructors plan.packet.context.interpretation plan.packet.declaration)
    (valid : GeneralNominalVersionedJournal232.Models state model) : Holds plan model ↔
    HeadModels plan.packet model ∧ SchemaHolds plan plan.headSchema model ∧ Outputs plan model ∧
    (∀ clause ∈ plan.packet.declaration.requirements, ∀ signature : clause.Signature roles,
      (childSchema plan clause signature).Holds (variables plan model) model) := by
  rw [GeneralNominalVersionedCurrentHead237.holds_iff plan frame valid]
  constructor
  · rintro ⟨head,schema,outputs,children⟩
    exact ⟨head,schema,outputs,fun clause member signature => (children clause member signature).2⟩
  · rintro ⟨head,schema,outputs,children⟩
    exact ⟨head,schema,outputs,fun clause member signature =>
      ⟨child_holds plan model covered (fun name named =>
        GeneralNominalVersionedCurrentHead237.capture_fits plan frame valid head schema name (Or.inl named))
        outputs clause member signature (children clause member signature),children clause member signature⟩⟩
theorem source_holds_iff (state : GeneralNominalVersionedJournal232.State roles) (plan : Plan roles) (model : Assignment)
    (path : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state)
    (frame : GeneralNominalVersionedEvidence231.Frame (GeneralNominalCenteredHeadAllocEncoding.registry registry)
      state.core focus key plan)
    (valid : GeneralNominalVersionedJournal232.Models state model) : Holds plan model ↔
    HeadModels plan.packet model ∧ SchemaHolds plan plan.headSchema model ∧ Outputs plan model ∧
    (∀ clause ∈ plan.packet.declaration.requirements, ∀ signature : clause.Signature roles,
      (childSchema plan clause signature).Holds (variables plan model) model) := by
  apply holds_iff state plan model frame _ valid
  have coverage : Coverage plan.packet.registry plan.packet.context.interpretation := by
    rw [frame.registry_eq,frame.context_eq]
    exact GeneralNominalVersionedMixedReady235.coverage path
  exact coverage.1 _ (frame.registry_eq.symm ▸ frame.visible)
end Yulang.GeneralNominalVersionedChildClosure237
