import Yulang.GeneralNominalProjectionCongruence238
import Yulang.GeneralDictionaryDefaultExpression209
import Yulang.GeneralNominalVersionedExpressionFrame236
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalSchemaCongruence238
open GeneralNominalAssignmentCongruence238 (Same subtype_iff)
open GeneralNominalOriginCongruence238 (observes inhabited_iff shared_iff head_iff)
open GeneralNominalRawCongruence238 (equiv_iff)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenters GeneralNominalMaterialization
open CommonNominalFullCarrier
variable {first last : Assignment}

theorem fits_iff (same : Same first last) (equal : Equivalent x y) (bounds : GeneralSourceState.Interval) :
 GeneralNominalCaptureMerges.Fits first bounds x ↔ GeneralNominalCaptureMerges.Fits last bounds y :=
 and_congr (subtype_iff (same _).1 equal) (subtype_iff equal (same _).1)

theorem site_iff (same : Same first last) (site : Site roles) : site.Holds first ↔ site.Holds last :=
 forall_congr' fun _index => fits_iff same (same _).1 _

theorem variable_iff (same : Same first last) (equal : Equivalent x y)
 (declaration : GeneralDeclarations.Declaration) (capture : GeneralDeclarationDemands.Capture) (name : Nat) (mode : Mode) :
 VariableHolds declaration capture first name mode x ↔ VariableHolds declaration capture last name mode y := by
 unfold VariableHolds
 split
 · exact equiv_iff equal (same _).1
 · cases mode with
   | lower | upper => exact equiv_iff equal (same _).1
   | actual => exact fits_iff same equal _

theorem transport_schema (same : Same first last) (plan : Plan roles) (schema : Schema)
 (valid : GeneralNominalVersionedPlans231.SchemaHolds plan schema first) :
 GeneralNominalVersionedPlans231.SchemaHolds plan schema last := by
 constructor
 · intro test member; exact (head_iff same _ _).mp (valid.1 test member)
 · intro entry member
   have old := valid.2 entry member
   by_cases actual : entry.mode = .actual
   · simp only [actual,ite_true] at old ⊢
     exact (shared_iff same _ _).mp old
   · simp only [actual,ite_false] at old ⊢
     refine ⟨(inhabited_iff same _).mp old.1,?_⟩
     intro value seen
     obtain ⟨before,observed,equal⟩ := observes (GeneralNominalAssignmentCongruence238.symm same) seen
     exact (variable_iff same ⟨equal.2,equal.1⟩ _ _ _ _).mp (old.2 before observed)

theorem schema_iff (same : Same first last) (plan : Plan roles) (schema : Schema) :
 GeneralNominalVersionedPlans231.SchemaHolds plan schema first ↔ GeneralNominalVersionedPlans231.SchemaHolds plan schema last :=
 ⟨transport_schema same plan schema,transport_schema (GeneralNominalAssignmentCongruence238.symm same) plan schema⟩

theorem variables (same : Same first last) (plan : Plan roles) (mode : Mode) (name : Nat) :
 Equivalent (GeneralNominalVersionedPlans231.variables plan first mode name)
 (GeneralNominalVersionedPlans231.variables plan last mode name) := by
 rw [GeneralNominalVersionedExpressionFrame236.variable_value,GeneralNominalVersionedExpressionFrame236.variable_value]
 exact (same _).1

theorem equation_iff (same : Same first last)
 (one two : Mode → Nat → Ty) (agree : ∀ mode name, Equivalent (one mode name) (two mode name))
 (equation : GeneralNominalCenteredHeadMatSchemas.Equation) :
 equation.Holds one first ↔ equation.Holds two last :=
 equiv_iff (same _).1 (GeneralDictionaryDefaultExpression209.value_equivalent equation.expression (fun mode name _ => agree mode name))

theorem total_schema_iff (same : Same first last)
 (one two : Mode → Nat → Ty) (agree : ∀ mode name, Equivalent (one mode name) (two mode name))
 (schema : GeneralNominalCenteredHeadMatSchemas.Schema) :
 schema.Holds one first ↔ schema.Holds two last :=
 forall_congr' fun equation => forall_congr' fun _ => equation_iff same one two agree equation

theorem versioned_total_schema_iff (same : Same first last) (plan : Plan roles)
 (schema : GeneralNominalCenteredHeadMatSchemas.Schema) :
 schema.Holds (GeneralNominalVersionedPlans231.variables plan first) first ↔
 schema.Holds (GeneralNominalVersionedPlans231.variables plan last) last :=
 total_schema_iff same _ _ (variables same plan) schema
end Yulang.GeneralNominalSchemaCongruence238
