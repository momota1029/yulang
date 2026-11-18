import Yulang.GeneralRebasePlanSemantic262
namespace Yulang.GeneralRebasePlanSemanticExamples262
open GeneralNominalCenters GeneralRebasePlanSemantic262

/-- Change positional center identities without changing the packet. This is
an arbitrary Plan transformation, not a certified source transition. -/
def recenter (plan : Plan roles) (center : Fin (roles plan.input.occurrence.demand.role).arity → Nat) : Plan roles :=
 {plan with input := {plan.input with center := center}}

theorem recenter_compatible (plan : Plan roles) (center)
 (cell : Core.PresenceGeneration.Comp CommonNominalFullCarrier.model) :
 Compatible plan (recenter plan center) (fun _ => cell) := by
 refine ⟨⟨rfl,rfl,rfl⟩,?_,?_⟩
 · intro name; exact GeneralDictionaryDefaultExpression209.equivalent_refl _
 · intro index; exact GeneralDictionaryDefaultExpression209.equivalent_refl _

theorem body_transport (plan : Plan roles) (center)
 (cell : Core.PresenceGeneration.Comp CommonNominalFullCarrier.model) (target)
 (body : GeneralDictionaryAssociatedProvenance.Body) :
 GeneralNominalVersionedEffects231.BodyHolds plan target (fun _ => cell) body ↔
 GeneralNominalVersionedEffects231.BodyHolds (recenter plan center) target (fun _ => cell) body :=
 body_holds plan _ _ (recenter_compatible plan center cell) body target

theorem structural_excluded (plan : Plan roles) (center)
 (index : Fin (roles plan.input.occurrence.demand.role).arity)
 (different : plan.input.center index ≠ center index) :
 ¬ GeneralRebasePlanTransport262.Same plan (recenter plan center) := by
 intro same
 have equal := congrArg (fun entries : List Nat => entries[index.val]?) same.centers
 apply different
 simpa [List.getElem?_ofFn,index.isLt,recenter] using equal

/-- Semantic compatibility is strictly weaker than structural center identity
whenever a positional input exists. No validity of the transformed source is
asserted, and no claim about every assignment is made. -/
theorem strict_weakening (plan : Plan roles)
 (index : Fin (roles plan.input.occurrence.demand.role).arity)
 (cell : Core.PresenceGeneration.Comp CommonNominalFullCarrier.model) :
 Compatible plan (recenter plan (fun i => plan.input.center i + 1)) (fun _ => cell) ∧
 ¬ GeneralRebasePlanTransport262.Same plan (recenter plan (fun i => plan.input.center i + 1)) :=
 ⟨recenter_compatible plan _ cell,
 structural_excluded plan _ index (Nat.ne_of_lt (Nat.lt_succ_self _))⟩
end Yulang.GeneralRebasePlanSemanticExamples262
