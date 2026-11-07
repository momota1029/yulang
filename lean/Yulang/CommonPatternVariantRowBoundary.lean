import Yulang.CommonPatternTyping
import Yulang.CommonRigidHeadInspection

/-!
# Distinct-tag producer unions do not encode payload-sensitive variant rows

The source specification already distinguishes variant rows from type union.
This module records why a merged-row bridge cannot replace such a row by an
ordinary union in the unchanged Common demand carrier. It is an obstruction
to that representation, not an E2 refutation of the full B2 target.
-/

namespace Yulang.CommonPatternVariantRowBoundary

open Common (Ty Row Subtype Equivalent)

theorem finite_distinct_tag_union_payload_erased (first last : Nat) (different : first ≠ last)
    (a b c d : CommonFinite.Ty Row) :
    CommonFinite.ProducerLe Common.rowLe (.union (.variant first a) (.variant last b))
      (.union (.variant first c) (.variant last d)) := by
  apply (CommonFinite.producerLe_iff_probe _ _).mpr
  intro rank environment observation accepted
  cases rank <;> cases observation <;>
    simp_all [CommonFinite.ProbeAt, CommonFinite.ProbeStep, CommonFinite.MaskedProbeStep]

/-- Arbitrary Common payloads, including regular graphs and arbitrary rows.
Only the two distinct tag heads remain observable in this producer union. -/
theorem distinct_tag_union_payload_erased (first last : Nat) (different : first ≠ last)
    (a b c d : Ty) :
    Equivalent (.union (Common.variant first a) (Common.variant last b))
      (.union (Common.variant first c) (Common.variant last d)) := by
  constructor <;> intro depth
  · exact finite_distinct_tag_union_payload_erased first last different _ _ _ _
  · exact finite_distinct_tag_union_payload_erased first last different _ _ _ _

/-- Every old Common upper bound admitting the two good variants also admits
the wrong payload at the first tag. Hence choosing a different old Common
upper bound cannot repair the ordinary-union row representation. -/
theorem upper_bound_payload_pollution (first last : Nat) (different : first ≠ last)
    (firstPayload lastPayload replacement target : Ty)
    (left : Subtype (Common.variant first firstPayload) target)
    (right : Subtype (Common.variant last lastPayload) target) :
    Subtype (Common.variant first replacement) target := by
  have original := (Common.common_union_is_join _ _ _).mpr ⟨left, right⟩
  exact Common.subtype_trans (CommonBoundCoalescing.le_union_left _ _)
    (Common.subtype_trans
      (distinct_tag_union_payload_erased first last different replacement lastPayload firstPayload lastPayload).1 original)

open Core.PresenceGeneration (Comp)
open Core.CommonData (ValueTyping)

def badValue : Core.CommonData.Value := .variant 0 (.literal (.str "wrong"))
def boundValue : CaseValues.Bindings Empty := [(0, .literal (.str "wrong"))]
def pattern : CasePatterns.Pattern Empty Empty := .variant 0 (.bind 0)
def floatCheck (value : Empty) (_ : Empty) : Bool := nomatch value
def defaultEval (_ : CaseValues.Bindings Empty) (code : Empty) :
    EvaluationTrace.Logged Unit Unit Core.CommonData.Value := nomatch code

theorem actual_bad_match :
    (ScopedCasePatterns.run floatCheck defaultEval [] pattern badValue).result = .ok (some boundValue) := rfl

/-- A minimal two-tag counterexample to payload-sensitive matching on an old
Common upper bound. The subject, successful match, and ill-typed returned
payload are all concrete; no evaluation oracle or default is involved. -/
theorem no_old_upper_bound_payload_safety (target : Ty)
    (left : Subtype (Common.variant 0 (.base .int)) target)
    (right : Subtype (Common.variant 1 (.base .str)) target) :
    ¬ (∀ value returned, ValueTyping Common.model value (Comp.pure Common.model target) →
      (ScopedCasePatterns.run floatCheck defaultEval [] pattern value).result = .ok (some returned) →
      CaseValues.BindingsHold (CommonPatternTyping.bindingTypes [(0, .base .int)]) returned) := by
  intro safe
  have payload : ValueTyping Common.model (.literal (.str "wrong"))
      (Comp.pure Common.model (.base .str)) :=
    .literal ⟨Common.subtype_refl _, Common.rowLe_refl _⟩
  have subject : ValueTyping Common.model badValue (Comp.pure Common.model target) :=
    .variant payload ⟨upper_bound_payload_pollution 0 1 (by decide) _ _ _ target left right,
      Common.rowLe_refl _⟩
  have returned := safe badValue boundValue subject actual_bad_match
  cases returned with
  | cons invalid rest =>
      change ValueTyping Common.model (.literal (.str "wrong")) (Comp.pure Common.model (.base .int)) at invalid
      cases invalid with
      | literal below =>
          have impossible := (CommonRigidHeadInspection.base_iff .str .int).mp below.1
          cases impossible

end Yulang.CommonPatternVariantRowBoundary
