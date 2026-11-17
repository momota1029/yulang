import Yulang.GeneralNominalVersionedPlans231
import Yulang.GeneralDictionaryDefaultSchema208

/-! I44 keeps explicit/default associated-output meanings unchanged: their
total expressions use actual centers, not versioned aggregate endpoints. -/
namespace Yulang.GeneralNominalVersionedEffects231
open GeneralNominalCenters GeneralNominalCommonBridge
open GeneralNominalCenteredHeadMatExpressions
open GeneralNominalMaterialization (Mode)
open CommonNominalFullCarrier
open GeneralDictionaryAssociatedProvenance
open GeneralDeclarations GeneralSourceDictionaries

mutual
  theorem actual_value (first last : Mode → Nat → Ty)
      (same : ∀ name, first .actual name = last .actual name) (expression : Expr) :
      value first .actual expression = value last .actual expression := by
    cases expression with
    | «variable» name => exact same name
    | primitive constructor args => simp only [value,actual_values first last same args]
    | nominal name args => simp only [value,actual_values first last same args]
    | record label a b => simp only [value,actual_value first last same a,actual_value first last same b]
    | variant tag a => simp only [value,actual_value first last same a]
    | join a b => simp only [value,actual_value first last same a,actual_value first last same b]
  theorem actual_values (first last : Mode → Nat → Ty)
      (same : ∀ name, first .actual name = last .actual name) (expressions : List Expr) :
      values first .actual expressions = values last .actual expressions := by
    cases expressions with
    | nil => rfl
    | cons head rest => simp only [values,actual_value first last same head,actual_values first last same rest]
end

theorem actual_expression (plan : Plan roles) (model : Assignment) (expression : Expr) :
    value (GeneralNominalVersionedPlans231.variables plan model) .actual expression =
      value (GeneralNominalCenteredHeadMatEffects.variables plan model) .actual expression :=
  actual_value _ _ (GeneralNominalVersionedPlans231.actual_variables plan model) expression

def bodyVariables (plan : Plan roles) (model : Assignment) : Body → Mode → Nat → Ty
  | .explicit _ => GeneralNominalVersionedPlans231.variables plan model
  | .default _ _ _ => GeneralNominalCenteredHeadMatEffects.defaultVariables plan model

def BodyHolds (plan : Plan roles) (target : Nat) (model : Assignment) (body : Body) : Prop :=
  (GeneralNominalCenteredHeadMatEffects.bodySchema plan target body).Holds (bodyVariables plan model body) model

theorem body_holds_iff (plan : Plan roles) (target : Nat) (model : Assignment) (body : Body) :
    BodyHolds plan target model body ↔ GeneralNominalCenteredHeadMatEffects.BodyHolds plan target model body := by
  unfold BodyHolds GeneralNominalCenteredHeadMatEffects.BodyHolds
  cases body with
  | default => rfl
  | explicit equation =>
    unfold GeneralNominalCenteredHeadMatEffects.bodySchema
    cases GeneralNominalCenteredHeadMatEffects.compileBody plan (.explicit equation) with
    | none => simp [GeneralNominalCenteredHeadMatSchemas.Schema.Holds]
    | some expression =>
      simp only [GeneralNominalCenteredHeadMatSchemas.Schema.Holds,List.mem_singleton,forall_eq]
      change Equivalent (model target).1 (value (GeneralNominalVersionedPlans231.variables plan model) .actual expression) ↔
        Equivalent (model target).1 (value (GeneralNominalCenteredHeadMatEffects.variables plan model) .actual expression)
      rw [actual_expression]

def ClassEffects (state : GeneralNominalCenteredSteps.State roles) (root : Occurrence roles)
    (plan : Plan roles) (model : Assignment) : Prop :=
  (∀ output ∈ GeneralNominalCenteredHeadOutputs.requests state root, ∀ body,
    lookup roles plan.packet.declaration output.name = some body → BodyHolds plan output.target model body) ∧
  GeneralNominalCenteredHeadOutputs.EqualOutputs state root model

theorem class_effects_iff (state : GeneralNominalCenteredSteps.State roles) (root : Occurrence roles)
    (plan : Plan roles) (model : Assignment) :
    ClassEffects state root plan model ↔ GeneralNominalCenteredHeadMatEffects.ClassEffects state root plan model := by
  unfold ClassEffects GeneralNominalCenteredHeadMatEffects.ClassEffects
  simp only [body_holds_iff]

def SchemaHolds (state : GeneralNominalCenteredSteps.State roles) (root : Occurrence roles)
    (plan : Plan roles) (model : Assignment) : Prop :=
  GeneralNominalVersionedPlans231.Outputs plan model ∧ ClassEffects state root plan model

theorem schema_holds_iff (state : GeneralNominalCenteredSteps.State roles) (root : Occurrence roles)
    (plan : Plan roles) (model : Assignment) :
    SchemaHolds state root plan model ↔ GeneralNominalVersionedPlans231.Outputs plan model ∧
      GeneralNominalCenteredHeadMatEffects.ClassEffects state root plan model := by
  unfold SchemaHolds
  rw [class_effects_iff]

end Yulang.GeneralNominalVersionedEffects231
