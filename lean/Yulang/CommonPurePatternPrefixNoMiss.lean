import Yulang.CommonPatternPrefixNoMiss

/-! Pure coverage witnesses retain their meaning in the prefix interpreter.
The theorem quantifies over every runtime pattern constructor, including
list direction, nominal identity and arbitrary float comparison. It makes
no assertion that Common has corresponding source typing rules. -/

namespace Yulang.CommonPurePatternPrefixNoMiss

open CaseValues (Value Bindings lookup)
open CasePatterns (Pattern)
open CommonPatternComputations (run)
open CommonPatternFinitePrefixes (Computation ops)
open CommonPatternPrefixNoMiss
open CommonPurePatternMatching (bindings combine_isSome)
open CommonCaseRecordMatching (accepts)

/-- Embed a callback-free source witness in an arbitrary default-code type.
Acceptance by the existing finite pure matcher excludes a completed miss
from the computation-polymorphic matcher on the same original value. -/
theorem pure_noMiss (floatCheck : F → F → Bool)
    (evaluate : Bindings F → D → Computation E R (Value F))
    (pattern : Pattern F Empty) (environment : Bindings F) (value : Value F)
    (accepted : accepts floatCheck pattern value = true) :
    NoMiss (run (ops E R) floatCheck evaluate environment (Core.Patterns.map Empty.elim pattern) value) := by
  induction pattern generalizing value environment with
  | wildcard | bind => exact ret_some_noMiss _
  | literal expected =>
      cases value <;> try cases accepted
      simp only [accepts, bindings] at accepted
      simp only [Core.Patterns.map, run]
      split
      · exact ret_some_noMiss _
      · simp_all
  | intRange lower upper =>
      cases value <;> try cases accepted
      simp only [accepts, bindings] at accepted
      simp only [Core.Patterns.map, run]
      split
      · exact ret_some_noMiss _
      · simp_all
  | pair p q ihp ihq =>
      cases value <;> try cases accepted
      simp only [accepts, bindings, combine_isSome, Bool.and_eq_true] at accepted
      exact andThen_noMiss _ _ (ihp environment _ accepted.1)
        (fun prior => ihq (prior ++ environment) _ accepted.2)
  | recordEnd =>
      cases value <;> try cases accepted
      exact ret_some_noMiss _
  | field name p rest ihp ihr =>
      cases value <;> try cases accepted
      rename_i fields
      rw [CommonCaseRecordMatching.accepts_field] at accepted
      simp only [Core.Patterns.map, run]
      cases found : lookup name fields with
      | none => simp only [found, Bool.false_eq_true] at accepted
      | some item =>
          simp only [found, Bool.and_eq_true] at accepted
          exact andThen_noMiss _ _ (ihp environment item accepted.1)
            (fun prior => ihr (prior ++ environment) (.record fields) accepted.2)
  | defaultField name impossible => exact impossible.elim
  | nil =>
      cases value <;> try cases accepted
      rename_i values
      cases values with
      | nil => exact ret_some_noMiss _
      | cons => cases accepted
  | cons p q ihp ihq =>
      cases value <;> try cases accepted
      rename_i values
      cases values with
      | nil => cases accepted
      | cons first rest =>
          simp only [accepts, bindings, combine_isSome, Bool.and_eq_true] at accepted
          exact andThen_noMiss _ _ (ihp environment first accepted.1)
            (fun prior => ihq (prior ++ environment) (.list rest) accepted.2)
  | snoc p q ihp ihq =>
      cases value <;> try cases accepted
      rename_i values
      simp only [accepts, bindings] at accepted
      simp only [Core.Patterns.map, run]
      cases reversed : values.reverse with
      | nil => simp only [reversed, Option.isSome_none, Bool.false_eq_true] at accepted
      | cons last rest =>
          simp only [reversed, combine_isSome, Bool.and_eq_true] at accepted
          exact andThen_noMiss _ _ (ihp environment (.list rest.reverse) accepted.1)
            (fun prior => ihq (prior ++ environment) last accepted.2)
  | variant tag p ih =>
      cases value <;> try cases accepted
      simp only [accepts, bindings] at accepted
      simp only [Core.Patterns.map, run]
      split
      · exact ih environment _ (by simpa [accepts, *] using accepted)
      · simp_all
  | nominal typeId ctorId p ih =>
      cases value <;> try cases accepted
      simp only [accepts, bindings] at accepted
      simp only [Core.Patterns.map, run]
      split
      · exact ih environment _ (by simpa [accepts, *] using accepted)
      · simp_all
  | or p q ihp ihq =>
      rw [CommonCaseRecordMatching.accepts_or, Bool.or_eq_true] at accepted
      rcases accepted with left | right
      · exact or_left_noMiss floatCheck evaluate environment _ _ value (ihp environment value left)
      · exact or_right_noMiss floatCheck evaluate environment _ _ value (ihq environment value right)
  | as p name ih =>
      rw [CommonCaseRecordMatching.accepts_as] at accepted
      exact as_noMiss floatCheck evaluate environment _ name value (ih environment value accepted)

/-- Finite joint-record coverage produces a no-miss source arm at every
actual domain record. Other arms may contain arbitrary executable defaults;
only the coverage witness is required to be a literal pure-source image. -/
theorem joint_record_witness (floatCheck : Empty → Empty → Bool)
    (evaluate : Bindings Empty → D → Computation E R (Value Empty)) (environment : Bindings Empty)
    (specification : CommonCaseRecordCells.Specification) (arms : List (CaseEvaluation.Arm Empty D G B))
    (coverage : CommonCaseRecordSourceCoverage.check floatCheck specification arms = true)
    (fields : Bindings Empty) (valid : CommonCaseRecordCells.Domain specification fields) :
    ∃ arm ∈ arms, arm.guard = none ∧
      NoMiss (run (ops E R) floatCheck evaluate environment arm.pattern (.record fields)) := by
  obtain ⟨pure, member, unguarded, accepted⟩ :=
    (CommonCaseRecordCoverage.check_exact floatCheck specification _).mp coverage fields valid
  obtain ⟨original, included, pattern, erased, rfl⟩ :=
    (CommonCaseRecordSourceCoverage.mem_pureArms arms pure).mp member
  refine ⟨original, included, unguarded, ?_⟩
  rw [← (CommonPurePatternErasure.erase_exact original.pattern pattern).mp erased]
  exact pure_noMiss floatCheck evaluate pattern environment (.record fields) accepted

end Yulang.CommonPurePatternPrefixNoMiss
