import Yulang.GeneralNominalOrderedOrigin248
import Yulang.GeneralRebaseRowBasis298

namespace Yulang.GeneralRebaseRowOrigin298
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
open GeneralNominalRebaseOriginView243
open GeneralPresenceUsedSupport245 (rowReads)
open GeneralRebaseRowBasis298

def support : Origin → List Nat
 | .source term => rowReads term
 | .nominal parent _ _ => support parent
 | .structural parent _ _ => support parent

theorem observes_forward (first last : Assignment)
 (types : ∀ n, (first n).1 = (last n).1)
 (seen : Observes first origin actual)
 (rows : ∀ n ∈ support origin, (first n).2 = (last n).2) : Observes last origin actual := by
 induction seen with
 | source term =>
   have equal := type_eval_equal model first last types term rows
   rw [equal]
   exact .source term
 | nominal seen equal found ih => exact .nominal (ih rows) equal found
 | structural seen length equal found ih => exact .structural (ih rows) length equal found

theorem observes_iff (origin : Origin) (first last : Assignment)
 (types : ∀ n, (first n).1 = (last n).1)
 (rows : ∀ n ∈ support origin, (first n).2 = (last n).2) (actual : Ty) :
 Observes first origin actual ↔ Observes last origin actual :=
 ⟨fun seen => observes_forward first last types seen rows,
 fun seen => observes_forward last first (fun n => (types n).symm) seen (fun n h => (rows n h).symm)⟩

theorem head_iff (origin : Origin) (test : GeneralNominalRecursiveInspection.Test) (first last : Assignment)
 (types : ∀ n, (first n).1 = (last n).1)
 (rows : ∀ n ∈ support origin, (first n).2 = (last n).2) :
 Head first origin test ↔ Head last origin test := by
 simp only [Head,observes_iff origin first last types rows]

theorem same_iff (a b : Origin) (first last : Assignment)
 (types : ∀ n, (first n).1 = (last n).1)
 (rows : ∀ n ∈ support a ++ support b, (first n).2 = (last n).2) :
 Same first a b ↔ Same last a b := by
 simp only [Same,observes_iff a first last types (fun n h => rows n (List.mem_append_left _ h)),
   observes_iff b first last types (fun n h => rows n (List.mem_append_right _ h))]
end Yulang.GeneralRebaseRowOrigin298
