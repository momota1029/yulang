import Yulang.CommonCaseStructuralCells
import Yulang.CommonCaseIntegerCoverage

/-! A callback-free source matcher on integer/product/variant values. Its
bindings and whole trace agree with the real scoped matcher on those values.
All source Pattern constructors are considered; unsupported root shapes miss. -/

namespace Yulang.CommonCaseStructuralMatching

open CaseValues EvaluationTrace
open CasePatterns (Pattern)
open CommonCaseStructuralCells (Supported ValueEquivalent)

def boundaries : Pattern F D → List Int
  | .literal (.int integer) => [integer]
  | .intRange lower upper => lower.toList ++ upper.toList
  | .pair first last | .field _ first last | .defaultField _ _ first last |
      .cons first last | .snoc first last | .or first last => boundaries first ++ boundaries last
  | .variant _ child | .nominal _ _ child | .as child _ => boundaries child
  | _ => []

def combine (first last : Option (Bindings F)) : Option (Bindings F) :=
  first.bind fun left => last.map (left ++ ·)

theorem combine_isSome (first last : Option (Bindings F)) :
    (combine first last).isSome = (first.isSome && last.isSome) := by cases first <;> cases last <;> rfl

def structuralBindings : Pattern F D → Value F → Option (Bindings F)
  | .wildcard, _ => some []
  | .bind name, value => some [(name, value)]
  | .literal (.int expected), .literal (.int actual) => if expected = actual then some [] else none
  | .intRange lower upper, .literal (.int integer) =>
      if LiteralValues.intRangeCheck lower upper (.int integer : LiteralValues.Literal F) then some [] else none
  | .pair first last, .pair left right => combine (structuralBindings first left) (structuralBindings last right)
  | .variant tag child, .variant actual payload => if tag = actual then structuralBindings child payload else none
  | .or first last, value => (structuralBindings first value).orElse (fun _ => structuralBindings last value)
  | .as child name, value => (structuralBindings child value).map ((name, value) :: ·)
  | _, _ => none

def accepts (pattern : Pattern F D) (value : Value F) : Bool := (structuralBindings pattern value).isSome

theorem bindings_integer (pattern : Pattern F D) (integer : Int) :
    structuralBindings pattern (.literal (.int integer)) = CommonCaseIntegerCoverage.integerBindings pattern integer := by
  induction pattern with
  | literal expected => cases expected <;> rfl
  | or first last ihf ihl => simp only [structuralBindings, CommonCaseIntegerCoverage.integerBindings, ihf, ihl]
  | as child name ih => simp only [structuralBindings, CommonCaseIntegerCoverage.integerBindings, ih]
  | _ => rfl

theorem accepts_integer (pattern : Pattern F D) (integer : Int) :
    accepts pattern (.literal (.int integer)) = CommonCaseIntegerCoverage.accepts pattern integer := by
  simp only [accepts, bindings_integer, CommonCaseIntegerCoverage.bindings_isSome]

theorem accepts_pair (first last : Pattern F D) (left right : Value F) :
    accepts (.pair first last) (.pair left right) = (accepts first left && accepts last right) :=
  combine_isSome _ _

theorem accepts_or (first last : Pattern F D) (value : Value F) :
    accepts (.or first last) value = (accepts first value || accepts last value) := by
  simp only [accepts, structuralBindings]
  cases structuralBindings first value <;> rfl

theorem accepts_as (child : Pattern F D) (name : Nat) (value : Value F) : accepts (.as child name) value = accepts child value :=
  Option.isSome_map

private theorem andThen_pure (first last : Option (Bindings F)) :
    ScopedCasePatterns.andThen (E := E) (R := R) (Logged.ofResult (.ok first)) (fun _ => Logged.ofResult (.ok last)) =
      Logged.ofResult (.ok (combine first last)) := by cases first <;> cases last <;> rfl

/-- Real binding payloads, binder order and empty trace are exact, for every
source pattern, arbitrary captured environment and default callback. -/
theorem run_supported_exact (floatCheck : F → F → Bool)
    (defaultEval : Bindings F → D → Logged E R (Value F)) (pattern : Pattern F D)
    (environment : Bindings F) (value : Value F) (supported : Supported value) :
    ScopedCasePatterns.run floatCheck defaultEval environment pattern value =
      Logged.ofResult (.ok (structuralBindings pattern value)) := by
  induction pattern generalizing environment value with
  | wildcard | bind => rfl
  | literal expected =>
      cases supported with
      | @integer integer =>
          rw [bindings_integer]
          exact CommonCaseIntegerCoverage.run_integer_exact floatCheck defaultEval environment _ integer
      | pair | variant => cases expected <;> rfl
  | intRange lower upper =>
      cases supported with
      | @integer integer =>
          rw [bindings_integer]
          exact CommonCaseIntegerCoverage.run_integer_exact floatCheck defaultEval environment _ integer
      | pair | variant => rfl
  | pair first last ihf ihl =>
      cases supported with
      | integer | variant => rfl
      | @pair left right sl sr =>
          simp only [ScopedCasePatterns.run, structuralBindings, ihf environment left sl]
          have next : (fun prior => ScopedCasePatterns.run floatCheck defaultEval (prior ++ environment) last right) =
              (fun _ => Logged.ofResult (.ok (structuralBindings last right))) :=
            funext fun prior => ihl (prior ++ environment) right sr
          rw [next]
          exact andThen_pure _ _
  | variant tag child ih =>
      cases supported with
      | integer | pair => rfl
      | @variant payload actual support =>
          simp only [ScopedCasePatterns.run, structuralBindings]
          split
          · exact ih environment payload support
          · rfl
  | or first last ihf ihl =>
      simp only [ScopedCasePatterns.run, structuralBindings, ihf environment value supported]
      cases structuralBindings first value <;>
        simp [Logged.bind, Logged.ofResult, ihl environment value supported, CasePatterns.success]
  | as child name ih =>
      simp only [ScopedCasePatterns.run, structuralBindings, ih environment value supported]
      cases structuralBindings child value <;> simp [Logged.bind, Logged.ofResult, CasePatterns.success, CasePatterns.miss]
  | recordEnd | field | defaultField | nil | cons | snoc | nominal => cases supported <;> rfl

theorem matches_supported_exact (floatCheck : F → F → Bool)
    (defaultEval : Bindings F → D → Logged E R (Value F)) (environment : Bindings F)
    (pattern : Pattern F D) (value : Value F) (supported : Supported value) :
    (∃ bindings, (ScopedCasePatterns.run floatCheck defaultEval environment pattern value).result = .ok (some bindings)) ↔
      accepts pattern value = true := by
  simp only [run_supported_exact floatCheck defaultEval pattern environment value supported, Logged.ofResult, Except.ok.injEq]
  exact Option.isSome_iff_exists.symm

theorem accepts_congr (pattern : Pattern F D) (same : ValueEquivalent bounds first last)
    (included : ∀ bound ∈ boundaries pattern, bound ∈ bounds) : accepts pattern first = accepts pattern last := by
  induction pattern generalizing first last with
  | wildcard | bind => rfl
  | literal expected =>
      cases expected <;> cases same
      all_goals try rfl
      rename_i bound first last comparisons
      rw [accepts_integer, accepts_integer]
      exact CommonCaseIntegerCoverage.accepts_same _ first last (fun point member => comparisons point (included point member))
  | intRange lower upper =>
      cases same with
      | @integer first last comparisons =>
          rw [accepts_integer, accepts_integer]
          exact CommonCaseIntegerCoverage.accepts_same _ first last (fun bound member => comparisons bound (included bound member))
      | pair | variant => rfl
  | pair p q ihp ihq =>
      cases same with
      | integer | variant => rfl
      | pair left right =>
          rw [accepts_pair, accepts_pair,
            ihp left (fun bound member => included bound (List.mem_append_left _ member)),
            ihq right (fun bound member => included bound (List.mem_append_right _ member))]
  | variant tag child ih =>
      cases same with
      | integer | pair => rfl
      | variant childSame =>
          simp only [accepts, structuralBindings]
          split
          · exact ih childSame included
          · rfl
  | or p q ihp ihq =>
      rw [accepts_or, accepts_or,
        ihp same (fun bound member => included bound (List.mem_append_left _ member)),
        ihq same (fun bound member => included bound (List.mem_append_right _ member))]
  | as child name ih => simpa only [accepts_as] using ih same included
  | recordEnd | field | defaultField | nil | cons | snoc | nominal => cases same <;> rfl

end Yulang.CommonCaseStructuralMatching
