import Yulang.GeneralRebasePlanTransport262
import Yulang.GeneralDictionaryDefaultExpression209
import Yulang.GeneralNominalRawCongruence238

namespace Yulang.GeneralRebasePlanSemantic262
open GeneralNominalCenters
open GeneralNominalCommonBridge (Assignment)
open GeneralSourceState (Output)
open GeneralRebaseStep258 (Fact)
open GeneralNominalMaterialization (Mode)
open GeneralNominalCenteredHeadMatExpressions (Expr value)
open CommonNominalFullCarrier

/-- Only syntactic compilation data. Actual binder identities may differ. -/
structure Layout (first last : Plan roles) : Prop where
 declaration : first.packet.declaration = last.packet.declaration
 constructors : first.packet.registry.constructors = last.packet.registry.constructors
 interpretation : first.packet.context.interpretation = last.packet.context.interpretation

/-- Agreement at one assignment, not at every possible assignment and not an
assumption about the desired output effects. Default centers retain positions. -/
structure Compatible (first last : Plan roles) (assignment : Assignment) : Prop where
 layout : Layout first last
 binders : ∀ name, Equivalent (assignment (first.binder name)).1 (assignment (last.binder name)).1
 centers : ∀ index : Nat, Equivalent
   (assignment ((List.ofFn first.input.center)[index]?.getD 0)).1
   (assignment ((List.ofFn last.input.center)[index]?.getD 0)).1

theorem of_structural (first last : Plan roles)
 (same : GeneralRebasePlanTransport262.Same first last) (assignment : Assignment) :
 Compatible first last assignment := by
 refine ⟨⟨same.declaration,same.constructors,same.interpretation⟩,?_,?_⟩
 · intro name
   rw [same.binders name]
   exact GeneralDictionaryDefaultExpression209.equivalent_refl _
 · intro index
   rw [same.centers]
   exact GeneralDictionaryDefaultExpression209.equivalent_refl _

theorem compile_eq (first last : Plan roles) (layout : Layout first last)
 (body : GeneralDictionaryAssociatedProvenance.Body) :
 GeneralNominalCenteredHeadMatEffects.compileBody first body =
 GeneralNominalCenteredHeadMatEffects.compileBody last body := by
 cases body <;> simp only [GeneralNominalCenteredHeadMatEffects.compileBody,layout.constructors,layout.interpretation]

theorem schema_eq (first last : Plan roles) (layout : Layout first last) (output : Output) :
 GeneralRebaseBodyTable261.schema first output = GeneralRebaseBodyTable261.schema last output := by
 unfold GeneralRebaseBodyTable261.schema
 rw [layout.declaration]
 cases GeneralDictionaryAssociatedProvenance.lookup roles last.packet.declaration output.name with
 | none => rfl
 | some body => simp only [GeneralNominalCenteredHeadMatEffects.bodySchema,compile_eq first last layout body]

theorem keys_eq (first last : Plan roles) (layout : Layout first last) (owner : Nat) (output : Output) :
 GeneralRebaseBodyTable261.keys first owner output = GeneralRebaseBodyTable261.keys last owner output := by
 unfold GeneralRebaseBodyTable261.keys
 rw [schema_eq first last layout output]

theorem facts_eq (first last : Plan roles) (layout : Layout first last) (owner : Nat) (outputs : List Output) :
 GeneralRebaseStableClass261.facts first owner outputs = GeneralRebaseStableClass261.facts last owner outputs := by
 unfold GeneralRebaseStableClass261.facts GeneralRebaseBodyTable261.facts
 have equal : GeneralRebaseBodyTable261.keys first owner = GeneralRebaseBodyTable261.keys last owner :=
   funext (keys_eq first last layout owner)
 rw [equal]

theorem actual_body_variables (first last : Plan roles) (assignment : Assignment)
 (compatible : Compatible first last assignment)
 (body : GeneralDictionaryAssociatedProvenance.Body) (name : Nat) :
 Equivalent (GeneralNominalVersionedEffects231.bodyVariables first assignment body .actual name)
 (GeneralNominalVersionedEffects231.bodyVariables last assignment body .actual name) := by
 cases body with
 | explicit equation =>
   simp only [GeneralNominalVersionedEffects231.bodyVariables,
     GeneralNominalVersionedPlans231.actual_variables,
     GeneralNominalCenteredHeadMatEffects.actual_variable]
   exact compatible.binders name
 | default role named term => exact compatible.centers name

theorem actual_variables (first last : Plan roles) (assignment : Assignment)
 (compatible : Compatible first last assignment) (output : Output) (name : Nat) :
 Equivalent (GeneralRebaseBodyTable261.variables first output assignment .actual name)
 (GeneralRebaseBodyTable261.variables last output assignment .actual name) := by
 unfold GeneralRebaseBodyTable261.variables
 rw [compatible.layout.declaration]
 cases GeneralDictionaryAssociatedProvenance.lookup roles last.packet.declaration output.name with
 | none => exact GeneralDictionaryDefaultExpression209.equivalent_refl _
 | some body => exact actual_body_variables first last assignment compatible body name

/-- Congruence for actual-mode evaluation only: endpoint modes may disagree. -/
theorem actual_value (first last : Mode → Nat → Ty)
 (same : ∀ name, Equivalent (first .actual name) (last .actual name)) (expression : Expr) :
 Equivalent (value first .actual expression) (value last .actual expression) := by
 rw [GeneralNominalVersionedEffects231.actual_value first (fun _ name => first .actual name) (fun _ => rfl),
   GeneralNominalVersionedEffects231.actual_value last (fun _ name => last .actual name) (fun _ => rfl)]
 exact GeneralDictionaryDefaultExpression209.value_equivalent expression (fun _ name _ => same name)

theorem owned_transport (owner : Nat) (schema : GeneralNominalCenteredHeadMatSchemas.Schema)
 (first last : Mode → Nat → Ty) (assignment : Assignment) (fact : Fact)
 (actual : ∀ equation ∈ schema.equations, equation.mode = .actual)
 (same : ∀ name, Equivalent (first .actual name) (last .actual name)) :
 GeneralRebaseOwnedOutputKeys260.Holds owner schema first assignment fact ↔
 GeneralRebaseOwnedOutputKeys260.Holds owner schema last assignment fact := by
 have equation (entry : GeneralNominalCenteredHeadMatSchemas.Equation) (member : entry ∈ schema.equations) :
     entry.Holds first assignment ↔ entry.Holds last assignment := by
   unfold GeneralNominalCenteredHeadMatSchemas.Equation.Holds
   rw [actual entry member]
   exact GeneralNominalRawCongruence238.equiv_iff
     (GeneralDictionaryDefaultExpression209.equivalent_refl _) (actual_value first last same entry.expression)
 constructor
 · rintro ⟨index,key,holds⟩
   exact ⟨index,key,(equation _ (List.getElem_mem index.isLt)).mp holds⟩
 · rintro ⟨index,key,holds⟩
   exact ⟨index,key,(equation _ (List.getElem_mem index.isLt)).mpr holds⟩

theorem local_holds (first last : Plan roles) (assignment : Assignment)
 (compatible : Compatible first last assignment) (owner : Nat) (output : Output) (fact : Fact) :
 GeneralRebaseBodyTable261.localHolds first owner output assignment fact ↔
 GeneralRebaseBodyTable261.localHolds last owner output assignment fact := by
 unfold GeneralRebaseBodyTable261.localHolds
 rw [← schema_eq first last compatible.layout output]
 exact owned_transport _ _ _ _ assignment fact (GeneralRebasePlanTransport262.schema_actual first output)
   (actual_variables first last assignment compatible output)

theorem stable_body_holds (first last : Plan roles) (assignment : Assignment)
 (compatible : Compatible first last assignment) (owner : Nat) (fact : Fact) :
 GeneralRebaseStableBody261.Holds first owner assignment fact ↔
 GeneralRebaseStableBody261.Holds last owner assignment fact := by
 constructor
 · intro holds output member
   exact (local_holds first last assignment compatible owner output fact).mp
     (holds output ((keys_eq first last compatible.layout owner output).symm ▸ member))
 · intro holds output member
   exact (local_holds first last assignment compatible owner output fact).mpr
     (holds output ((keys_eq first last compatible.layout owner output) ▸ member))

theorem stable_class_holds (first last : Plan roles) (assignment : Assignment)
 (compatible : Compatible first last assignment) (owner : Nat) (fact : Fact) :
 GeneralRebaseStableClass261.Holds first owner assignment fact ↔
 GeneralRebaseStableClass261.Holds last owner assignment fact :=
 and_congr (stable_body_holds first last assignment compatible owner fact) Iff.rfl

theorem body_holds (first last : Plan roles) (assignment : Assignment)
 (compatible : Compatible first last assignment)
 (body : GeneralDictionaryAssociatedProvenance.Body) (target : Nat) :
 GeneralNominalVersionedEffects231.BodyHolds first target assignment body ↔
 GeneralNominalVersionedEffects231.BodyHolds last target assignment body := by
 unfold GeneralNominalVersionedEffects231.BodyHolds GeneralNominalCenteredHeadMatEffects.bodySchema
 rw [← compile_eq first last compatible.layout body]
 cases translated : GeneralNominalCenteredHeadMatEffects.compileBody first body with
 | none => simp [GeneralNominalCenteredHeadMatSchemas.Schema.Holds]
 | some expression =>
   simp only [GeneralNominalCenteredHeadMatSchemas.Schema.Holds,List.mem_singleton,forall_eq]
   unfold GeneralNominalCenteredHeadMatSchemas.Equation.Holds
   exact GeneralNominalRawCongruence238.equiv_iff
     (GeneralDictionaryDefaultExpression209.equivalent_refl _)
     (actual_value _ _ (actual_body_variables first last assignment compatible body) expression)

theorem effects (first last : Plan roles) (assignment : Assignment)
 (compatible : Compatible first last assignment) (outputs : List Output) :
 GeneralRebaseClassTable261.Effects first outputs assignment ↔
 GeneralRebaseClassTable261.Effects last outputs assignment := by
 unfold GeneralRebaseClassTable261.Effects
 simp only [compatible.layout.declaration,body_holds first last assignment compatible]

theorem class_effects (first last : Plan roles) (assignment : Assignment)
 (compatible : Compatible first last assignment)
 (source : GeneralNominalCenteredSteps.State roles) (root : GeneralSourceDictionaries.Occurrence roles) :
 GeneralNominalVersionedEffects231.ClassEffects source root first assignment ↔
 GeneralNominalVersionedEffects231.ClassEffects source root last assignment := effects first last assignment compatible _

end Yulang.GeneralRebasePlanSemantic262
