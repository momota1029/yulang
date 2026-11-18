import Yulang.GeneralNominalOriginSupport249
import Yulang.GeneralNominalRebaseSchemaView243

namespace Yulang.GeneralNominalSchemaSupport249
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
open GeneralNominalRebaseSchemaView243
open GeneralNominalRebaseOriginView243 (Observes)
open GeneralPresenceUsedSupport245 (typedReads)
open GeneralPresenceConsumerSupport246

def requirementReads : Requirement → List Nat
 | .equal term => typedReads term
 | .interval lo hi => typedReads lo ++ typedReads hi

def useReads : Use → List Nat
 | .same a b => GeneralNominalOriginSupport249.support a ++ GeneralNominalOriginSupport249.support b
 | .observed origin requirement => GeneralNominalOriginSupport249.support origin ++ requirementReads requirement

def support (schema : Schema) : List Nat :=
 schema.tests.flatMap (fun t => GeneralNominalOriginSupport249.support t.1) ++ schema.uses.flatMap useReads

theorem requirement_iff (r : Requirement) (first last : Assignment)
 (rows : ∀ n, (first n).2 = (last n).2)
 (types : ∀ n ∈ requirementReads r, (first n).1 = (last n).1) (actual : Ty) :
 r.Holds first actual ↔ r.Holds last actual := by
 cases r with
 | equal term => simp only [Requirement.Holds,type_eval_equal model first last rows term types]
 | interval lo hi => simp only [Requirement.Holds,
   type_eval_equal model first last rows lo (fun n h => types n (List.mem_append_left _ h)),
   type_eval_equal model first last rows hi (fun n h => types n (List.mem_append_right _ h))]

theorem use_iff (u : Use) (first last : Assignment)
 (rows : ∀ n, (first n).2 = (last n).2)
 (types : ∀ n ∈ useReads u, (first n).1 = (last n).1) : u.Holds first ↔ u.Holds last := by
 cases u with
 | same a b => exact GeneralNominalOriginSupport249.same_iff a b first last rows types
 | observed origin requirement =>
   simp only [Use.Holds,GeneralNominalOriginSupport249.observes_iff origin first last rows
     (fun n h => types n (List.mem_append_left _ h)),
     requirement_iff requirement first last rows (fun n h => types n (List.mem_append_right _ h))]

theorem schema_iff (schema : Schema) (first last : Assignment)
 (rows : ∀ n, (first n).2 = (last n).2)
 (types : ∀ n ∈ support schema, (first n).1 = (last n).1) : schema.Holds first ↔ schema.Holds last := by
 apply and_congr
 · apply forall_congr'; intro test
   apply forall_congr'; intro member
   exact GeneralNominalOriginSupport249.head_iff test.1 test.2 first last rows
     (fun n h => types n (List.mem_append_left _ (List.mem_flatMap.mpr ⟨test,member,h⟩)))
 · apply forall_congr'; intro use
   apply forall_congr'; intro member
   exact use_iff use first last rows
     (fun n h => types n (List.mem_append_right _ (List.mem_flatMap.mpr ⟨use,member,h⟩)))
end Yulang.GeneralNominalSchemaSupport249
