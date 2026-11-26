import Yulang.GeneralDeclarativeI65I74CompletedLowerPayload437
import Yulang.GeneralDeclarativeI65I72TypedTargetRows403

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.CompletedLower437

open CommonNominalFullCarrier (Equivalent)
open GeneralDeclarativeHead320 (environment)
open GeneralNominalCenteredHeadMatExpressions (value)
open I72 (fixedValueCode403 fixed_value_code_same_model403)

/-- Read the value from this exact retained row, in the same model as
the original typed occurrence. The lower's nativeSyntax is unused. -/
theorem retained_literal_typed_output_means_same_lower437 {s : State} {L receipt}
    (p : Payload (s := s) L receipt)
    (code : fixedValueCode403 receipt.rhs = some p.code) (m : Model) (fit : Fits s m) :
    p.Means m := by
  have eq := fixed_value_code_same_model403 receipt.rhs m p.code code
  have kept := fit.1.1.2 _ (List.mem_of_getElem? p.row)
  refine ⟨value (environment m.assignment) .actual p.code,?_,kept⟩
  simp only [NamedMixedReceipt401.actualEquation,eq,Option.map_some,p.target]

/-- The exact same B6 plan also evaluates to that very lower value;
neither a nominal tag check nor a freely chosen ordinary encoding
is an adequate substitute. No completion is inferred at this layer. -/
theorem lower_retention_uses_original_B6_value437 {s q atlas frame i}
    (out : NamedMixedOutput401 (s := s) (q := q) atlas frame i) {L : Nat}
    (p : Payload L out.receipt) (code : fixedValueCode403 out.rhs = some p.code)
    (m : Model) (fit : Fits s m) :
    ∃ v, atlas.read q frame.ordinal i out.body = some out.plan ∧
      evaluateMixedRhs401 (sourceRead401 m (frame.slots out.body)) out.plan = some v ∧
      out.receipt.actualEquation m = some (L,v) ∧ Equivalent (m.assignment L).1 v := by
  obtain ⟨original,atOriginal,fromPlan⟩ := named_mixed_output_is_fixed_equation401 out m
  obtain ⟨kept,atLower,meaning⟩ := retained_literal_typed_output_means_same_lower437 p code m fit
  have sameValue : original = kept := congrArg Prod.snd (Option.some.inj (atOriginal.symm.trans atLower))
  rw [sameValue] at fromPlan
  exact ⟨kept,out.originalTyped,fromPlan,atLower,meaning⟩

end Yulang.GeneralDeclarativeI65.CompletedLower437
