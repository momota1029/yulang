import Yulang.CommonCaseBaseCells
import Yulang.CommonCaseLiteralCoverage

/-! Real source matching and cell invariance for all Common literal bases
under arbitrary nested products and single-tag variants. No default executes
on these supported values; all source constructors are still quantified. -/

namespace Yulang.CommonCaseBaseMatching

open CaseValues EvaluationTrace
open CasePatterns (Pattern)
open CommonCaseBaseCells (Supported ValueEquivalent)

def boundaries : Pattern Empty D → List Int
  | .literal (.int integer) => [integer]
  | .intRange lower upper => lower.toList ++ upper.toList
  | .pair first last | .field _ first last | .defaultField _ _ first last |
      .cons first last | .snoc first last | .or first last => boundaries first ++ boundaries last
  | .variant _ child | .nominal _ _ child | .as child _ => boundaries child
  | _ => []

def texts : Pattern Empty D → List String
  | .literal (.str text) => [text]
  | .pair first last | .field _ first last | .defaultField _ _ first last |
      .cons first last | .snoc first last | .or first last => texts first ++ texts last
  | .variant _ child | .nominal _ _ child | .as child _ => texts child
  | _ => []

def combine (first last : Option (Bindings Empty)) : Option (Bindings Empty) :=
  first.bind fun left => last.map (left ++ ·)

theorem combine_isSome (first last : Option (Bindings Empty)) :
    (combine first last).isSome = (first.isSome && last.isSome) := by cases first <;> cases last <;> rfl

def structuralBindings : Pattern Empty D → Value Empty → Option (Bindings Empty)
  | .wildcard, _ => some []
  | .bind name, value => some [(name, value)]
  | .literal expected, .literal actual => if expected = actual then some [] else none
  | .intRange lower upper, .literal actual =>
      if LiteralValues.intRangeCheck lower upper actual then some [] else none
  | .pair first last, .pair left right => combine (structuralBindings first left) (structuralBindings last right)
  | .variant tag child, .variant actual payload => if tag = actual then structuralBindings child payload else none
  | .or first last, value => (structuralBindings first value).orElse (fun _ => structuralBindings last value)
  | .as child name, value => (structuralBindings child value).map ((name, value) :: ·)
  | _, _ => none

def accepts (pattern : Pattern Empty D) (value : Value Empty) : Bool := (structuralBindings pattern value).isSome

theorem bindings_literal (pattern : Pattern Empty D) (literal : LiteralValues.Literal Empty) :
    structuralBindings pattern (.literal literal) = CommonCaseLiteralCoverage.literalBindings pattern literal := by
  induction pattern with
  | literal expected => rfl
  | or first last ihf ihl => simp only [structuralBindings, CommonCaseLiteralCoverage.literalBindings, ihf, ihl]
  | as child name ih => simp only [structuralBindings, CommonCaseLiteralCoverage.literalBindings, ih]
  | _ => rfl

theorem accepts_literal (pattern : Pattern Empty D) (literal : LiteralValues.Literal Empty) :
    accepts pattern (.literal literal) = CommonCaseLiteralCoverage.accepts pattern literal := by
  simp only [accepts, bindings_literal, CommonCaseLiteralCoverage.bindings_isSome]

theorem accepts_pair (first last : Pattern Empty D) (left right : Value Empty) :
    accepts (.pair first last) (.pair left right) = (accepts first left && accepts last right) :=
  combine_isSome _ _

theorem accepts_or (first last : Pattern Empty D) (value : Value Empty) :
    accepts (.or first last) value = (accepts first value || accepts last value) := by
  simp only [accepts, structuralBindings]
  cases structuralBindings first value <;> rfl

theorem accepts_as (child : Pattern Empty D) (name : Nat) (value : Value Empty) : accepts (.as child name) value = accepts child value :=
  Option.isSome_map

private theorem andThen_pure (first last : Option (Bindings Empty)) :
    ScopedCasePatterns.andThen (E := E) (R := R) (Logged.ofResult (.ok first)) (fun _ => Logged.ofResult (.ok last)) =
      Logged.ofResult (.ok (combine first last)) := by cases first <;> cases last <;> rfl

/-- Real binding payloads, binder order and empty trace are exact, for every
source pattern, arbitrary captured environment and default callback. -/
theorem run_supported_exact (floatCheck : Empty → Empty → Bool)
    (defaultEval : Bindings Empty → D → Logged E R (Value Empty)) (pattern : Pattern Empty D)
    (environment : Bindings Empty) (value : Value Empty) (supported : Supported value) :
    ScopedCasePatterns.run floatCheck defaultEval environment pattern value =
      Logged.ofResult (.ok (structuralBindings pattern value)) := by
  induction pattern generalizing environment value with
  | wildcard | bind => rfl
  | literal expected =>
      cases supported with
      | @literal actual =>
          rw [bindings_literal]
          exact CommonCaseLiteralCoverage.run_literal_exact floatCheck defaultEval environment _ actual
      | pair | variant => rfl
  | intRange lower upper =>
      cases supported with
      | @literal actual =>
          rw [bindings_literal]
          exact CommonCaseLiteralCoverage.run_literal_exact floatCheck defaultEval environment _ actual
      | pair | variant => rfl
  | pair first last ihf ihl =>
      cases supported with
      | literal | variant => rfl
      | @pair left right sl sr =>
          simp only [ScopedCasePatterns.run, structuralBindings, ihf environment left sl]
          have next : (fun prior => ScopedCasePatterns.run floatCheck defaultEval (prior ++ environment) last right) =
              (fun _ => Logged.ofResult (.ok (structuralBindings last right))) :=
            funext fun prior => ihl (prior ++ environment) right sr
          rw [next]
          exact andThen_pure _ _
  | variant tag child ih =>
      cases supported with
      | literal | pair => rfl
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

theorem matches_supported_exact (floatCheck : Empty → Empty → Bool)
    (defaultEval : Bindings Empty → D → Logged E R (Value Empty)) (environment : Bindings Empty)
    (pattern : Pattern Empty D) (value : Value Empty) (supported : Supported value) :
    (∃ bindings, (ScopedCasePatterns.run floatCheck defaultEval environment pattern value).result = .ok (some bindings)) ↔
      accepts pattern value = true := by
  simp only [run_supported_exact floatCheck defaultEval pattern environment value supported, Logged.ofResult, Except.ok.injEq]
  exact Option.isSome_iff_exists.symm

theorem accepts_congr (pattern : Pattern Empty D) (same : ValueEquivalent bounds strings first last)
    (boundsIncluded : ∀ bound ∈ boundaries pattern, bound ∈ bounds)
    (textsIncluded : ∀ text ∈ texts pattern, text ∈ strings) : accepts pattern first = accepts pattern last := by
  induction pattern generalizing first last with
  | wildcard | bind => rfl
  | literal expected =>
      cases same with
      | literal scalar =>
          rw [accepts_literal, accepts_literal]
          exact CommonCaseLiteralCoverage.accepts_congr _ scalar
            (fun bound member => boundsIncluded bound (by cases expected <;> exact member))
            (fun text member => textsIncluded text (by cases expected <;> exact member))
      | pair | variant => rfl
  | intRange lower upper =>
      cases same with
      | literal scalar =>
          rw [accepts_literal, accepts_literal]
          exact CommonCaseLiteralCoverage.accepts_congr _ scalar boundsIncluded textsIncluded
      | pair | variant => rfl
  | pair p q ihp ihq =>
      cases same with
      | literal | variant => rfl
      | pair left right =>
          rw [accepts_pair, accepts_pair,
            ihp left (fun bound member => boundsIncluded bound (List.mem_append_left _ member))
              (fun text member => textsIncluded text (List.mem_append_left _ member)),
            ihq right (fun bound member => boundsIncluded bound (List.mem_append_right _ member))
              (fun text member => textsIncluded text (List.mem_append_right _ member))]
  | variant tag child ih =>
      cases same with
      | literal | pair => rfl
      | variant childSame =>
          simp only [accepts, structuralBindings]
          split
          · exact ih childSame boundsIncluded textsIncluded
          · rfl
  | or p q ihp ihq =>
      rw [accepts_or, accepts_or,
        ihp same (fun bound member => boundsIncluded bound (List.mem_append_left _ member))
          (fun text member => textsIncluded text (List.mem_append_left _ member)),
        ihq same (fun bound member => boundsIncluded bound (List.mem_append_right _ member))
          (fun text member => textsIncluded text (List.mem_append_right _ member))]
  | as child name ih => simpa only [accepts_as] using ih same boundsIncluded textsIncluded
  | recordEnd | field | defaultField | nil | cons | snoc | nominal => cases same <;> rfl

end Yulang.CommonCaseBaseMatching
