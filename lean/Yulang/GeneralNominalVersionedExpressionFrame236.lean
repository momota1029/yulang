import Yulang.GeneralNominalVersionedPlans231
import Yulang.GeneralNominalCenteredFrame179
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalVersionedExpressionFrame236
open GeneralNominalCenteredHeadMatExpressions GeneralNominalCenteredHeadMatSchemas
open GeneralNominalMaterialization (Mode)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenters
open GeneralNominalCenteredFrame179 (Agree)
open CommonNominalFullCarrier

private theorem congrTwo (f : α → β → γ) {a b : α} {c d : β} (one : a=b) (two : c=d) : f a c = f b d := by cases one; cases two; rfl

mutual
 def reads (mode : Mode) : Expr → List (Mode × Nat)
  | .variable name => [(mode,name)]
  | .primitive _ arguments => readsMany mode arguments
  | .nominal _ arguments => readsMany .actual arguments
  | .record _ a b | .join a b => reads mode a ++ reads mode b
  | .variant _ a => reads mode a
 def readsMany (mode : Mode) : List Expr → List (Mode × Nat)
  | [] => []
  | a :: rest => reads mode a ++ readsMany mode rest
end
mutual
 theorem value_eq (first last : Mode → Nat → Ty) (mode : Mode) (expression : Expr)
     (same : ∀ key ∈ reads mode expression, first key.1 key.2 = last key.1 key.2) :
     value first mode expression = value last mode expression := by
   cases expression with
   | «variable» name => exact same (mode,name) (List.mem_singleton_self _)
   | primitive constructor args => exact congrArg (primitiveValue constructor) (values_eq first last mode args same)
   | nominal name args => exact congrArg (fun xs => nominal name (xs.map Sum.inl)) (values_eq first last .actual args same)
   | record label a b =>
     exact congrTwo (record label)
       (value_eq first last mode a (fun k h => same k (List.mem_append_left _ h)))
       (value_eq first last mode b (fun k h => same k (List.mem_append_right _ h)))
   | variant tag a => exact congrArg (variant tag) (value_eq first last mode a same)
   | join a b =>
     exact congrTwo (fun a b : Ty => (.union a b : Ty))
       (value_eq first last mode a (fun k h => same k (List.mem_append_left _ h)))
       (value_eq first last mode b (fun k h => same k (List.mem_append_right _ h)))
 theorem values_eq (first last : Mode → Nat → Ty) (mode : Mode) (expressions : List Expr)
     (same : ∀ key ∈ readsMany mode expressions, first key.1 key.2 = last key.1 key.2) :
     values first mode expressions = values last mode expressions := by
   cases expressions with
   | nil => rfl
   | cons a rest =>
     exact congrTwo List.cons
       (value_eq first last mode a (fun k h => same k (List.mem_append_left _ h)))
       (values_eq first last mode rest (fun k h => same k (List.mem_append_right _ h)))
end

def variableSource (plan : Plan roles) (mode : Mode) (name : Nat) : Nat :=
  if name ∈ plan.packet.declaration.outputNames then GeneralNominalVersionedFrame231.binder plan name
  else match mode with
  | .actual => GeneralNominalVersionedFrame231.binder plan name
  | .lower => ((GeneralNominalVersionedFrame231.capture plan.packet).inputs name).1
  | .upper => ((GeneralNominalVersionedFrame231.capture plan.packet).inputs name).2

theorem variable_value (plan : Plan roles) (model : Assignment) (mode name) :
    GeneralNominalVersionedPlans231.variables plan model mode name = (model (variableSource plan mode name)).1 := by
  unfold GeneralNominalVersionedPlans231.variables variableSource
  split <;> first | rfl | cases mode <;> rfl

def equationSources (plan : Plan roles) (equation : Equation) : List Nat :=
  equation.target :: (reads equation.mode equation.expression).map (fun key => variableSource plan key.1 key.2)
def schemaSources (plan : Plan roles) (schema : Schema) : List Nat := schema.equations.flatMap (equationSources plan)

theorem equation_iff (plan : Plan roles) (equation : Equation) {first last : Assignment}
    (same : Agree (equationSources plan equation) first last) :
    equation.Holds (GeneralNominalVersionedPlans231.variables plan first) first ↔
      equation.Holds (GeneralNominalVersionedPlans231.variables plan last) last := by
  have expression := value_eq (GeneralNominalVersionedPlans231.variables plan first)
    (GeneralNominalVersionedPlans231.variables plan last) equation.mode equation.expression (by
      intro key member
      simp only [variable_value]
      exact congrArg Prod.fst (same _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨key,member,rfl⟩))))
  unfold Equation.Holds
  rw [same _ List.mem_cons_self,expression]

theorem schema_iff (plan : Plan roles) (schema : Schema) {first last : Assignment}
    (same : Agree (schemaSources plan schema) first last) :
    schema.Holds (GeneralNominalVersionedPlans231.variables plan first) first ↔
      schema.Holds (GeneralNominalVersionedPlans231.variables plan last) last := by
  apply forall_congr'; intro equation
  apply forall_congr'; intro member
  exact equation_iff plan equation (fun name present => same name (List.mem_flatMap.mpr ⟨equation,member,present⟩))
end Yulang.GeneralNominalVersionedExpressionFrame236
