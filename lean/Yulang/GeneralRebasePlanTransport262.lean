import Yulang.GeneralRebaseStableClass261
import Yulang.GeneralNominalCenteredHeadMatPlanData

namespace Yulang.GeneralRebasePlanTransport262
open GeneralNominalCenters
open GeneralNominalCommonBridge (Assignment)
open GeneralSourceState (Output)
open GeneralRebaseStep258 (Fact)
open GeneralNominalMaterialization (Mode)
open GeneralNominalCenteredHeadMatExpressions (value)

/-- Structural data sufficient for retaining output fact meanings. Lower and
upper captures, journal contents and observation history need not be equal. -/
structure Same (first last : Plan roles) : Prop where
 declaration : first.packet.declaration = last.packet.declaration
 constructors : first.packet.registry.constructors = last.packet.registry.constructors
 interpretation : first.packet.context.interpretation = last.packet.context.interpretation
 binders : ∀ name, first.binder name = last.binder name
 centers : List.ofFn first.input.center = List.ofFn last.input.center

theorem of_report_data (first last : Plan roles)
 (same : GeneralNominalCenteredHeadMatPlanData.Same first last) : Same first last := by
 refine ⟨same.declaration,congrArg GeneralDeclarations.Registry.constructors same.registry,
   same.interpretation,GeneralNominalCenteredHeadMatPlanData.binder same,?_⟩
 rw [same.input]

theorem compile_eq (first last : Plan roles) (same : Same first last)
 (body : GeneralDictionaryAssociatedProvenance.Body) :
 GeneralNominalCenteredHeadMatEffects.compileBody first body =
 GeneralNominalCenteredHeadMatEffects.compileBody last body := by
 cases body <;> simp only [GeneralNominalCenteredHeadMatEffects.compileBody,same.constructors,same.interpretation]

theorem schema_eq (first last : Plan roles) (same : Same first last) (output : Output) :
 GeneralRebaseBodyTable261.schema first output = GeneralRebaseBodyTable261.schema last output := by
 unfold GeneralRebaseBodyTable261.schema
 rw [same.declaration]
 cases GeneralDictionaryAssociatedProvenance.lookup roles last.packet.declaration output.name with
 | none => rfl
 | some body => simp only [GeneralNominalCenteredHeadMatEffects.bodySchema,compile_eq first last same body]

theorem actual_body_variables (first last : Plan roles) (same : Same first last)
 (assignment : Assignment) (body : GeneralDictionaryAssociatedProvenance.Body) (name : Nat) :
 GeneralNominalVersionedEffects231.bodyVariables first assignment body .actual name =
 GeneralNominalVersionedEffects231.bodyVariables last assignment body .actual name := by
 cases body with
 | explicit equation =>
   simp only [GeneralNominalVersionedEffects231.bodyVariables,
     GeneralNominalVersionedPlans231.actual_variables,
     GeneralNominalCenteredHeadMatEffects.actual_variable,same.binders name]
   rfl
 | default role named term =>
   simp only [GeneralNominalVersionedEffects231.bodyVariables,
     GeneralNominalCenteredHeadMatEffects.defaultVariables,same.centers]
   rfl

theorem actual_variables (first last : Plan roles) (same : Same first last)
 (output : Output) (assignment : Assignment) (name : Nat) :
 GeneralRebaseBodyTable261.variables first output assignment .actual name =
 GeneralRebaseBodyTable261.variables last output assignment .actual name := by
 unfold GeneralRebaseBodyTable261.variables
 rw [same.declaration]
 cases GeneralDictionaryAssociatedProvenance.lookup roles last.packet.declaration output.name with
 | none => rfl
 | some body => exact actual_body_variables first last same assignment body name

theorem schema_actual (plan : Plan roles) (output : Output)
 (equation : GeneralNominalCenteredHeadMatSchemas.Equation)
 (member : equation ∈ (GeneralRebaseBodyTable261.schema plan output).equations) : equation.mode = .actual := by
 unfold GeneralRebaseBodyTable261.schema at member
 cases found : GeneralDictionaryAssociatedProvenance.lookup roles plan.packet.declaration output.name with
 | none => simp only [found,List.not_mem_nil] at member
 | some body =>
   simp only [found,GeneralNominalCenteredHeadMatEffects.bodySchema] at member
   cases translated : GeneralNominalCenteredHeadMatEffects.compileBody plan body with
   | none => simp only [translated,List.not_mem_nil] at member
   | some expression =>
     simp only [translated,List.mem_singleton] at member
     cases member
     rfl

theorem owned_transport (owner : Nat) (schema : GeneralNominalCenteredHeadMatSchemas.Schema)
 (first last : Mode → Nat → CommonNominalFullCarrier.Ty) (assignment : Assignment) (fact : Fact)
 (actual : ∀ equation ∈ schema.equations, equation.mode = .actual)
 (same : ∀ name, first .actual name = last .actual name) :
 GeneralRebaseOwnedOutputKeys260.Holds owner schema first assignment fact ↔
 GeneralRebaseOwnedOutputKeys260.Holds owner schema last assignment fact := by
 have equation (entry : GeneralNominalCenteredHeadMatSchemas.Equation) (member : entry ∈ schema.equations) :
     entry.Holds first assignment ↔ entry.Holds last assignment := by
   unfold GeneralNominalCenteredHeadMatSchemas.Equation.Holds
   rw [actual entry member,GeneralNominalVersionedEffects231.actual_value first last same]
 constructor
 · rintro ⟨index,key,holds⟩
   exact ⟨index,key,(equation _ (List.getElem_mem index.isLt)).mp holds⟩
 · rintro ⟨index,key,holds⟩
   exact ⟨index,key,(equation _ (List.getElem_mem index.isLt)).mpr holds⟩

theorem keys_eq (first last : Plan roles) (same : Same first last) (owner : Nat) (output : Output) :
 GeneralRebaseBodyTable261.keys first owner output = GeneralRebaseBodyTable261.keys last owner output := by
 unfold GeneralRebaseBodyTable261.keys
 rw [schema_eq first last same output]

theorem local_holds (first last : Plan roles) (same : Same first last) (owner : Nat)
 (output : Output) (assignment : Assignment) (fact : Fact) :
 GeneralRebaseBodyTable261.localHolds first owner output assignment fact ↔
 GeneralRebaseBodyTable261.localHolds last owner output assignment fact := by
 unfold GeneralRebaseBodyTable261.localHolds
 rw [← schema_eq first last same output]
 exact owned_transport _ _ _ _ assignment fact (schema_actual first output)
   (actual_variables first last same output assignment)

theorem stable_body_holds (first last : Plan roles) (same : Same first last) (owner : Nat)
 (assignment : Assignment) (fact : Fact) :
 GeneralRebaseStableBody261.Holds first owner assignment fact ↔
 GeneralRebaseStableBody261.Holds last owner assignment fact := by
 constructor
 · intro holds output member
   exact (local_holds first last same owner output assignment fact).mp
     (holds output ((keys_eq first last same owner output).symm ▸ member))
 · intro holds output member
   exact (local_holds first last same owner output assignment fact).mpr
     (holds output ((keys_eq first last same owner output) ▸ member))

theorem stable_class_holds (first last : Plan roles) (same : Same first last) (owner : Nat)
 (assignment : Assignment) (fact : Fact) :
 GeneralRebaseStableClass261.Holds first owner assignment fact ↔
 GeneralRebaseStableClass261.Holds last owner assignment fact :=
 and_congr (stable_body_holds first last same owner assignment fact) Iff.rfl

theorem facts_eq (first last : Plan roles) (same : Same first last) (owner : Nat) (outputs : List Output) :
 GeneralRebaseStableClass261.facts first owner outputs = GeneralRebaseStableClass261.facts last owner outputs := by
 unfold GeneralRebaseStableClass261.facts GeneralRebaseBodyTable261.facts
 have equal : GeneralRebaseBodyTable261.keys first owner = GeneralRebaseBodyTable261.keys last owner :=
   funext (keys_eq first last same owner)
 rw [equal]

theorem body_holds (first last : Plan roles) (same : Same first last)
 (body : GeneralDictionaryAssociatedProvenance.Body) (target : Nat) (assignment : Assignment) :
 GeneralNominalVersionedEffects231.BodyHolds first target assignment body ↔
 GeneralNominalVersionedEffects231.BodyHolds last target assignment body := by
 unfold GeneralNominalVersionedEffects231.BodyHolds GeneralNominalCenteredHeadMatEffects.bodySchema
 rw [← compile_eq first last same body]
 cases translated : GeneralNominalCenteredHeadMatEffects.compileBody first body with
 | none => simp [GeneralNominalCenteredHeadMatSchemas.Schema.Holds]
 | some expression =>
   simp only [GeneralNominalCenteredHeadMatSchemas.Schema.Holds,List.mem_singleton,forall_eq]
   unfold GeneralNominalCenteredHeadMatSchemas.Equation.Holds
   rw [GeneralNominalVersionedEffects231.actual_value _ _ (actual_body_variables first last same assignment body)]

theorem effects (first last : Plan roles) (same : Same first last)
 (outputs : List Output) (assignment : Assignment) :
 GeneralRebaseClassTable261.Effects first outputs assignment ↔
 GeneralRebaseClassTable261.Effects last outputs assignment := by
 unfold GeneralRebaseClassTable261.Effects
 simp only [same.declaration,body_holds first last same]

theorem class_effects (first last : Plan roles) (same : Same first last)
 (source : GeneralNominalCenteredSteps.State roles) (root : GeneralSourceDictionaries.Occurrence roles)
 (assignment : Assignment) :
 GeneralNominalVersionedEffects231.ClassEffects source root first assignment ↔
 GeneralNominalVersionedEffects231.ClassEffects source root last assignment := effects first last same _ assignment

end Yulang.GeneralRebasePlanTransport262
