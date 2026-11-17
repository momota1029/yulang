import Yulang.GeneralNominalRebaseSchemaView243
import Yulang.GeneralNominalRebaseOriginActivation243
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalRebaseSchemaSupport243
open GeneralNominalRebaseSchemaView243
open GeneralNominalRebaseOriginActivation243 (sources observes_iff head_iff same_iff)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredFrame179 (Agree)
open GeneralNominalState (typeSources)

def requirementSources : Requirement → List Nat
 | .equal term => typeSources term
 | .interval lo hi => typeSources lo ++ typeSources hi

def useSources : Use → List Nat
 | .same origin target => sources origin ++ sources target
 | .observed origin requirement => sources origin ++ requirementSources requirement

def schemaSources (schema : Schema) : List Nat :=
 schema.tests.flatMap (fun test => sources test.1) ++ schema.uses.flatMap useSources

theorem requirement_iff (requirement : Requirement) {first last : Assignment}
 (same : Agree (requirementSources requirement) first last) (actual) :
 requirement.Holds first actual ↔ requirement.Holds last actual := by
 cases requirement with
 | equal term =>
   have equal := GeneralNominalCenteredModelExtension.type_eval_same term same
   simp only [Requirement.Holds,equal]
 | interval lo hi =>
   have lower := GeneralNominalCenteredModelExtension.type_eval_same lo
     (fun name member => same name (List.mem_append_left _ member))
   have upper := GeneralNominalCenteredModelExtension.type_eval_same hi
     (fun name member => same name (List.mem_append_right _ member))
   simp only [Requirement.Holds,lower,upper]

theorem use_iff (use : Use) {first last : Assignment}
 (same : Agree (useSources use) first last) : use.Holds first ↔ use.Holds last := by
 cases use with
 | same origin target => exact same_iff origin target same
 | observed origin requirement =>
   have observed := observes_iff origin
     (fun name member => same name (List.mem_append_left _ member))
   have required := requirement_iff requirement
     (fun name member => same name (List.mem_append_right _ member))
   simp only [Use.Holds,observed,required]

theorem models_iff (schema : Schema) {first last : Assignment}
 (same : Agree (schemaSources schema) first last) : schema.Holds first ↔ schema.Holds last := by
 apply and_congr
 · apply forall_congr'; intro test
   apply forall_congr'; intro member
   exact head_iff test.1 (fun name present => same name
     (List.mem_append_left _ (List.mem_flatMap.mpr ⟨test,member,present⟩))) test.2
 · apply forall_congr'; intro use
   apply forall_congr'; intro member
   exact use_iff use (fun name present => same name
     (List.mem_append_right _ (List.mem_flatMap.mpr ⟨use,member,present⟩)))
end Yulang.GeneralNominalRebaseSchemaSupport243
