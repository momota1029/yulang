import Yulang.CommonPatternFinitePrefixes
import Yulang.CommonRecordNoMiss

/-! Coverage certificates for completed finite prefixes of the actual
computation-polymorphic matcher. Defaults may fail, diverge or have several
possible observations. A no-miss conclusion excludes a completed mismatch;
it never asserts that a computation returns. -/

namespace Yulang.CommonPatternPrefixNoMiss

open CaseValues (Value Bindings lookup)
open CasePatterns (Pattern)
open CommonPatternComputations (run andThen align)
open CommonPatternFinitePrefixes (Computation Observation Bind ret ops)
open CommonPatternNoMiss (EveryValue)

def Returns (computation : Computation E R A) (value : A) : Prop :=
  ∃ trace, computation ⟨trace, some (.ok value)⟩

@[simp] theorem returns_ret (first last : A) :
    Returns (ret (E := E) (R := R) first) last ↔ last = first := by
  constructor
  · rintro ⟨trace, absent | completed⟩
    · cases absent
    · cases completed
      rfl
  · rintro rfl
    exact ⟨[], Or.inr rfl⟩

theorem returns_bind (first : Computation E R A) (next : A → Computation E R B) (value : B) :
    Returns (Bind first next) value ↔ ∃ prior, Returns first prior ∧ Returns (next prior) value := by
  constructor
  · rintro ⟨trace, present⟩
    have completed (observed : Observation E R B) (within : Bind first next observed) :
        observed.result = some (.ok value) →
          ∃ prior, Returns first prior ∧ Returns (next prior) value := by
      cases within with
      | pending => intro impossible; cases impossible
      | error => intro impossible; cases impossible
      | returned earlier prior later head tail =>
          intro same
          refine ⟨prior, ⟨earlier, head⟩, ⟨later.trace, ?_⟩⟩
          cases later with
          | mk events result =>
              simp only at same
              cases same
              exact tail
    exact completed _ present rfl
  · rintro ⟨prior, ⟨earlier, head⟩, ⟨later, tail⟩⟩
    exact ⟨earlier ++ later, .returned earlier prior ⟨later, some (.ok value)⟩ head tail⟩

def NoMiss (computation : Computation E R (Option A)) : Prop := ¬ Returns computation none

theorem ret_some_noMiss (value : A) : NoMiss (ret (E := E) (R := R) (some value)) := by
  simp [NoMiss]

theorem bind_noMiss (first : Computation E R A) (next : A → Computation E R (Option B))
    (after : ∀ value, Returns first value → NoMiss (next value)) : NoMiss (Bind first next) := by
  intro missed
  obtain ⟨value, firstReturned, nextReturned⟩ := (returns_bind first next none).mp missed
  exact after value firstReturned nextReturned

theorem andThen_noMiss (first : Computation E R (Option (Bindings F)))
    (next : Bindings F → Computation E R (Option (Bindings F)))
    (head : NoMiss first) (tail : ∀ prior, NoMiss (next prior)) :
    NoMiss (andThen (ops E R) first next) := by
  apply bind_noMiss
  intro option returned
  cases option with
  | none => exact False.elim (head returned)
  | some prior =>
      apply bind_noMiss
      intro option returned
      cases option with
      | none => exact False.elim (tail prior returned)
      | some more => exact ret_some_noMiss _

theorem align_noMiss (names : List Nat) (first : Computation E R (Option (Bindings F)))
    (head : NoMiss first) : NoMiss (align (ops E R) names first) := by
  apply bind_noMiss
  intro option returned
  cases option with
  | none => exact False.elim (head returned)
  | some values => exact ret_some_noMiss _

theorem or_left_noMiss (floatCheck : F → F → Bool)
    (evaluate : Bindings F → D → Computation E R (Value F)) (environment : Bindings F)
    (p q : Pattern F D) (value : Value F)
    (left : NoMiss (run (ops E R) floatCheck evaluate environment p value)) :
    NoMiss (run (ops E R) floatCheck evaluate environment (.or p q) value) := by
  apply align_noMiss
  apply bind_noMiss
  intro option returned
  cases option with
  | none => exact False.elim (left returned)
  | some values => exact ret_some_noMiss _

theorem or_right_noMiss (floatCheck : F → F → Bool)
    (evaluate : Bindings F → D → Computation E R (Value F)) (environment : Bindings F)
    (p q : Pattern F D) (value : Value F)
    (right : NoMiss (run (ops E R) floatCheck evaluate environment q value)) :
    NoMiss (run (ops E R) floatCheck evaluate environment (.or p q) value) := by
  apply align_noMiss
  apply bind_noMiss
  intro option returned
  cases option with
  | none => exact right
  | some values => exact ret_some_noMiss _

theorem as_noMiss (floatCheck : F → F → Bool)
    (evaluate : Bindings F → D → Computation E R (Value F)) (environment : Bindings F)
    (pattern : Pattern F D) (name : Nat) (value : Value F)
    (child : NoMiss (run (ops E R) floatCheck evaluate environment pattern value)) :
    NoMiss (run (ops E R) floatCheck evaluate environment (.as pattern name) value) := by
  apply bind_noMiss
  intro option returned
  cases option with
  | none => exact False.elim (child returned)
  | some values => exact ret_some_noMiss _

/-- Any source pattern certified for every value cannot finish with a miss,
even when an earlier alternative contains a nonterminating default. -/
theorem everyValue_noMiss (floatCheck : F → F → Bool)
    (evaluate : Bindings F → D → Computation E R (Value F))
    (total : EveryValue pattern) (environment : Bindings F) (value : Value F) :
    NoMiss (run (ops E R) floatCheck evaluate environment pattern value) := by
  induction total with
  | wildcard | bind => exact ret_some_noMiss _
  | orLeft left ih => exact or_left_noMiss floatCheck evaluate environment _ _ value ih
  | orRight right ih => exact or_right_noMiss floatCheck evaluate environment _ _ value ih
  | as child ih => exact as_noMiss floatCheck evaluate environment _ _ value ih

/-- A successful finite base-cell pattern cannot finish with a miss in the
prefix interpreter. Supported values contain literals, pairs and single-tag
variants, so an arbitrary source default callback is never needed here. -/
theorem supported_noMiss (floatCheck : Empty → Empty → Bool)
    (evaluate : Bindings Empty → D → Computation E R (Value Empty))
    (pattern : Pattern Empty D) (environment : Bindings Empty) (value : Value Empty)
    (supported : CommonCaseBaseCells.Supported value)
    (accepted : CommonCaseBaseMatching.accepts pattern value = true) :
    NoMiss (run (ops E R) floatCheck evaluate environment pattern value) := by
  induction pattern generalizing value environment with
  | wildcard | bind => exact ret_some_noMiss _
  | literal expected =>
      cases supported with
      | literal =>
          simp only [CommonCaseBaseMatching.accepts, CommonCaseBaseMatching.structuralBindings] at accepted
          simp only [run, CommonCaseLiteralCoverage.matchCheck_empty, decide_eq_true_eq]
          split
          · exact ret_some_noMiss _
          · simp_all
      | pair | variant => cases accepted
  | intRange lower upper =>
      cases supported with
      | literal =>
          simp only [CommonCaseBaseMatching.accepts, CommonCaseBaseMatching.structuralBindings] at accepted
          simp only [run]
          split
          · exact ret_some_noMiss _
          · simp_all
      | pair | variant => cases accepted
  | pair p q ihp ihq =>
      cases supported with
      | literal | variant => cases accepted
      | pair first last =>
          rw [CommonCaseBaseMatching.accepts_pair] at accepted
          have parts := Bool.and_eq_true_iff.mp accepted
          exact andThen_noMiss _ _ (ihp environment _ first parts.1)
            (fun prior => ihq (prior ++ environment) _ last parts.2)
  | variant tag p ih =>
      cases supported with
      | literal | pair => cases accepted
      | variant child =>
          simp only [CommonCaseBaseMatching.accepts, CommonCaseBaseMatching.structuralBindings] at accepted
          simp only [run]
          split
          · exact ih environment _ child (by simpa [CommonCaseBaseMatching.accepts, *] using accepted)
          · simp_all
  | or p q ihp ihq =>
      rw [CommonCaseBaseMatching.accepts_or, Bool.or_eq_true] at accepted
      rcases accepted with left | right
      · exact or_left_noMiss floatCheck evaluate environment p q value (ihp environment value supported left)
      · exact or_right_noMiss floatCheck evaluate environment p q value (ihq environment value supported right)
  | as p name ih =>
      rw [CommonCaseBaseMatching.accepts_as] at accepted
      exact as_noMiss floatCheck evaluate environment p name value (ih environment value supported accepted)
  | recordEnd | field | defaultField | nil | cons | snoc | nominal => cases supported <;> cases accepted

/-- The existing independently defined record certificate retains its
meaning for every finite-prefix callback. In particular, a missing-field
default may never complete; no callback result or termination is a premise. -/
theorem record_noMiss (floatCheck : Empty → Empty → Bool)
    (evaluate : Bindings Empty → D → Computation E R (Value Empty))
    (total : CommonRecordNoMiss.Total specification pattern)
    (fields : Bindings Empty) (valid : CommonCaseRecordCells.Domain specification fields)
    (environment : Bindings Empty) :
    NoMiss (run (ops E R) floatCheck evaluate environment pattern (.record fields)) := by
  induction total generalizing environment with
  | wildcard | bind | recordEnd => exact ret_some_noMiss _
  | field known rest ih =>
      obtain ⟨shape, member, covered⟩ := known
      obtain ⟨item, found, itemValid⟩ := valid _ member
      simp only [run, found]
      exact andThen_noMiss _ _
        (supported_noMiss floatCheck evaluate _ environment item itemValid.supported (covered item itemValid))
        (fun prior => ih (prior ++ environment))
  | @defaultAny p rest name code child restTyped ih =>
      apply bind_noMiss
      intro value _
      exact andThen_noMiss _ _ (everyValue_noMiss floatCheck evaluate child environment value)
        (fun prior => ih (prior ++ environment))
  | @defaultKnown name p rest code known restTyped ih =>
      obtain ⟨shape, member, covered⟩ := known
      obtain ⟨item, found, itemValid⟩ := valid _ member
      simp only [run, found]
      apply bind_noMiss
      intro value returned
      have same := (returns_ret item value).mp returned
      subst value
      exact andThen_noMiss _ _
        (supported_noMiss floatCheck evaluate p environment item itemValid.supported (covered item itemValid))
        (fun prior => ih (prior ++ environment))
  | orLeft left ih => exact or_left_noMiss floatCheck evaluate environment _ _ (.record fields) (ih environment)
  | orRight right ih => exact or_right_noMiss floatCheck evaluate environment _ _ (.record fields) (ih environment)
  | as child ih => exact as_noMiss floatCheck evaluate environment _ _ (.record fields) (ih environment)

end Yulang.CommonPatternPrefixNoMiss
