import Yulang.GeneralNominalOrderedOrigin248
import Yulang.GeneralPresenceConsumerSupport246

/-! Literal source evaluation equality yields same-witness observations for
all actual expression origins, including source leaves. No Stable premise. -/
namespace Yulang.GeneralNominalOriginSupport249
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
open GeneralNominalRebaseOriginView243
open GeneralPresenceUsedSupport245 (typedReads)
open GeneralPresenceConsumerSupport246

def support : Origin → List Nat
 | .source term => typedReads term
 | .nominal parent _ _ => support parent
 | .structural parent _ _ => support parent

theorem observes_forward (first last : Assignment)
 (rows : ∀ n, (first n).2 = (last n).2)
 (seen : Observes first origin actual)
 (types : ∀ n ∈ support origin, (first n).1 = (last n).1) : Observes last origin actual := by
 induction seen with
 | source term =>
   have equal := type_eval_equal model first last rows term types
   rw [equal]
   exact .source term
 | nominal seen equal found ih => exact .nominal (ih types) equal found
 | structural seen length equal found ih => exact .structural (ih types) length equal found

theorem observes_iff (origin : Origin) (first last : Assignment)
 (rows : ∀ n, (first n).2 = (last n).2)
 (types : ∀ n ∈ support origin, (first n).1 = (last n).1) (actual : Ty) :
 Observes first origin actual ↔ Observes last origin actual :=
 ⟨fun seen => observes_forward first last rows seen types,
 fun seen => observes_forward last first (fun n => (rows n).symm) seen (fun n h => (types n h).symm)⟩

theorem head_iff (origin : Origin) (test : GeneralNominalRecursiveInspection.Test) (first last : Assignment)
 (rows : ∀ n, (first n).2 = (last n).2)
 (types : ∀ n ∈ support origin, (first n).1 = (last n).1) :
 Head first origin test ↔ Head last origin test := by
 simp only [Head,observes_iff origin first last rows types]

theorem same_iff (a b : Origin) (first last : Assignment)
 (rows : ∀ n, (first n).2 = (last n).2)
 (types : ∀ n ∈ support a ++ support b, (first n).1 = (last n).1) :
 Same first a b ↔ Same last a b := by
 simp only [Same,observes_iff a first last rows (fun n h => types n (List.mem_append_left _ h)),
   observes_iff b first last rows (fun n h => types n (List.mem_append_right _ h))]
end Yulang.GeneralNominalOriginSupport249
