import Yulang.GeneralNominalVersionedExpressionFrame236
import Yulang.GeneralDictionaryDefaultExpression209
import Yulang.GeneralNominalVersionedEffects231

namespace Yulang.GeneralRebaseRowIrrelevance273
open CommonNominalFullCarrier
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRecursiveInspection (Origin Observes Report Fits ProjectionModels)
open GeneralNominalCenters (Plan Site)
open GeneralNominalVersionedPlans231 (variables)

def SameTypes (first last : Assignment) : Prop := ∀ id, (first id).1 = (last id).1

theorem symm (same : SameTypes first last) : SameTypes last first := fun id => (same id).symm

theorem observes (same : SameTypes first last) (observed : Observes first origin value) :
 Observes last origin value := by
 induction observed with
 | source id => rw [same id]; exact .source id
 | nominal _ held present ih => exact .nominal ih held present
 | structural _ arity held present ih => exact .structural ih arity held present

theorem occurs (same : SameTypes first last) (origin : Origin) (t : Ty) :
 Observes first origin t ↔ Observes last origin t :=
 ⟨observes same,observes (symm same)⟩

theorem head (same : SameTypes first last) (origin : Origin) (test : GeneralNominalRecursiveInspection.Test) :
 GeneralNominalOriginTerms.Head first origin test ↔ GeneralNominalOriginTerms.Head last origin test := by
 simp only [GeneralNominalOriginTerms.Head,occurs same]

theorem shared (same : SameTypes first last) (a b : Origin) :
 GeneralNominalOriginTerms.Same first a b ↔ GeneralNominalOriginTerms.Same last a b := by
 simp only [GeneralNominalOriginTerms.Same,occurs same]

theorem capture (same : SameTypes first last) (bounds : GeneralSourceState.Interval) (t : Ty) :
 GeneralNominalCaptureMerges.Fits first bounds t ↔ GeneralNominalCaptureMerges.Fits last bounds t := by
 exact and_congr (by rw [same bounds.1]) (by rw [same bounds.2])

theorem site (same : SameTypes first last) (site : Site roles) : site.Holds first ↔ site.Holds last := by
 apply forall_congr'; intro index
 rw [same (site.center index)]
 exact capture same _ _

theorem projection (same : SameTypes first last) (s : GeneralNominalState.State) (r : Report s) :
 ProjectionModels s r first ↔ ProjectionModels s r last := by
 simp only [ProjectionModels,Fits,occurs same,capture same]

theorem environment (same : SameTypes first last) (plan : Plan roles) :
 variables plan first = variables plan last := by
 funext mode name
 simp only [GeneralNominalVersionedExpressionFrame236.variable_value]
 exact same _

theorem equation (same : SameTypes first last) (plan : Plan roles)
 (equation : GeneralNominalCenteredHeadMatSchemas.Equation) :
 equation.Holds (variables plan first) first ↔ equation.Holds (variables plan last) last := by
 rw [GeneralNominalCenteredHeadMatSchemas.Equation.Holds,GeneralNominalCenteredHeadMatSchemas.Equation.Holds,environment same plan,same]

theorem schema (same : SameTypes first last) (plan : Plan roles)
 (schema : GeneralNominalCenteredHeadMatSchemas.Schema) :
 schema.Holds (variables plan first) first ↔ schema.Holds (variables plan last) last :=
 forall_congr' fun item => forall_congr' fun _ => equation same plan item

theorem variable_iff (same : SameTypes first last) (declaration : GeneralDeclarations.Declaration)
 (c : GeneralDeclarationDemands.Capture) (name : Nat) (mode : GeneralNominalMaterialization.Mode) (t : Ty) :
 GeneralNominalMaterialization.VariableHolds declaration c first name mode t ↔
 GeneralNominalMaterialization.VariableHolds declaration c last name mode t := by
 unfold GeneralNominalMaterialization.VariableHolds
 split
 · rw [same]
 · cases mode
   · change Equivalent t (first (c.inputs name).1).1 ↔ Equivalent t (last (c.inputs name).1).1
     rw [same]
   · change Equivalent t (first (c.inputs name).2).1 ↔ Equivalent t (last (c.inputs name).2).1
     rw [same]
   · exact capture same _ _

theorem head_schema (same : SameTypes first last) (plan : Plan roles)
 (schema : GeneralNominalMaterialization.Schema) :
 GeneralNominalVersionedPlans231.SchemaHolds plan schema first ↔
 GeneralNominalVersionedPlans231.SchemaHolds plan schema last := by
 apply and_congr
 · exact forall_congr' fun entry => forall_congr' fun _ => head same entry.1 entry.2
 · apply forall_congr'; intro entry
   apply forall_congr'; intro _
   by_cases actual : entry.mode = .actual
   · simp only [actual,ite_true,shared same]
   · simp only [actual,ite_false,occurs same,variable_iff same]

open GeneralNominalVersionedEffects231 (bodyVariables BodyHolds ClassEffects)

theorem body_environment (same : SameTypes first last) (plan : Plan roles)
 (body : GeneralDictionaryAssociatedProvenance.Body) :
 bodyVariables plan first body = bodyVariables plan last body := by
 cases body with
 | explicit => exact environment same plan
 | default =>
   funext mode name
   exact same _

theorem body_iff (same : SameTypes first last) (plan : Plan roles)
 (target : Nat) (body : GeneralDictionaryAssociatedProvenance.Body) :
 BodyHolds plan target first body ↔ BodyHolds plan target last body := by
 unfold BodyHolds
 rw [body_environment same plan body]
 apply forall_congr'; intro equation
 apply forall_congr'; intro _
 unfold GeneralNominalCenteredHeadMatSchemas.Equation.Holds
 rw [same equation.target]

theorem live (same : SameTypes first last) (core : GeneralNominalCenteredSteps.State roles)
 (root : GeneralSourceDictionaries.Occurrence roles) (plan : Plan roles) :
 ClassEffects core root plan first ↔ ClassEffects core root plan last := by
 unfold ClassEffects
 apply and_congr
 · exact forall_congr' fun output => forall_congr' fun _ =>
     forall_congr' fun body => forall_congr' fun _ => body_iff same plan output.target body
 · unfold GeneralNominalCenteredHeadOutputs.EqualOutputs
   exact forall_congr' fun a => forall_congr' fun _ =>
     forall_congr' fun b => forall_congr' fun _ => forall_congr' fun _ => by rw [same a.target,same b.target]

end Yulang.GeneralRebaseRowIrrelevance273
