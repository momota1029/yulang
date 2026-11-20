import Yulang.GeneralRebaseRowOrigin298
import Yulang.GeneralNominalRebaseSchemaView243

namespace Yulang.GeneralRebaseRowSchema298
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
open GeneralNominalRebaseSchemaView243
open GeneralNominalRebaseOriginView243 (Observes)
open GeneralPresenceUsedSupport245 (rowReads)
open GeneralRebaseRowBasis298

def requirementReads : Requirement → List Nat
 | .equal term => rowReads term
 | .interval lo hi => rowReads lo ++ rowReads hi

def useReads : Use → List Nat
 | .same a b => GeneralRebaseRowOrigin298.support a ++ GeneralRebaseRowOrigin298.support b
 | .observed origin requirement => GeneralRebaseRowOrigin298.support origin ++ requirementReads requirement

def support (schema : Schema) : List Nat :=
 schema.tests.flatMap (fun t => GeneralRebaseRowOrigin298.support t.1) ++ schema.uses.flatMap useReads

theorem requirement_iff (r : Requirement) (first last : Assignment)
 (types : ∀ n, (first n).1 = (last n).1)
 (rows : ∀ n ∈ requirementReads r, (first n).2 = (last n).2) (actual : Ty) :
 r.Holds first actual ↔ r.Holds last actual := by
 cases r with
 | equal term => simp only [Requirement.Holds,type_eval_equal model first last types term rows]
 | interval lo hi => simp only [Requirement.Holds,
   type_eval_equal model first last types lo (fun n h => rows n (List.mem_append_left _ h)),
   type_eval_equal model first last types hi (fun n h => rows n (List.mem_append_right _ h))]

theorem use_iff (u : Use) (first last : Assignment)
 (types : ∀ n, (first n).1 = (last n).1)
 (rows : ∀ n ∈ useReads u, (first n).2 = (last n).2) : u.Holds first ↔ u.Holds last := by
 cases u with
 | same a b => exact GeneralRebaseRowOrigin298.same_iff a b first last types rows
 | observed origin requirement =>
   simp only [Use.Holds,GeneralRebaseRowOrigin298.observes_iff origin first last types
     (fun n h => rows n (List.mem_append_left _ h)),
     requirement_iff requirement first last types (fun n h => rows n (List.mem_append_right _ h))]

theorem schema_iff (schema : Schema) (first last : Assignment)
 (types : ∀ n, (first n).1 = (last n).1)
 (rows : ∀ n ∈ support schema, (first n).2 = (last n).2) : schema.Holds first ↔ schema.Holds last := by
 apply and_congr
 · apply forall_congr'; intro test
   apply forall_congr'; intro member
   exact GeneralRebaseRowOrigin298.head_iff test.1 test.2 first last types
     (fun n h => rows n (List.mem_append_left _ (List.mem_flatMap.mpr ⟨test,member,h⟩)))
 · apply forall_congr'; intro use
   apply forall_congr'; intro member
   exact use_iff use first last types
     (fun n h => rows n (List.mem_append_right _ (List.mem_flatMap.mpr ⟨use,member,h⟩)))
end Yulang.GeneralRebaseRowSchema298
