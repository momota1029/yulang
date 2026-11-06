import Yulang.FoldListSpread
import Yulang.NominalListSpread

/-!
# The existing finite-list spread kernel as a protocol special case

The old logged evaluator is embedded by exposing each observation as a signed
unit-response request, and each existing failure as an abortive request. This
embedding preserves the old evaluator; it does not assign a language operation
name to those abstract observations or errors.

A successfully resolved list traverses its actual finite contents. For every
old `NominalListSpread.Meaning` derivation, the new machine returns exactly the
same flattened list and exactly one copy of the source trace, in source order.
Successful finite evaluation is used only for this correspondence theorem;
the general protocol safety/progress theorems do not assume it.
-/

namespace Yulang.FoldListSpreadFinite

open Directed SignatureRequests EvaluationTrace CaseValues
open FoldListSpread

def signature (Event Error : Type) : Signature (Event ⊕ Error) where
  Payload _ := Unit
  Response
    | .inl _ => Unit
    | .inr _ => Empty

def sourceView : Logged Event Error (Value F) →
    FoldListSpread.View n (signature Event Error) (Value F) (Logged Event Error (Value F))
  | ⟨[], .ok value⟩ => .value value
  | ⟨[], .error error⟩ => .request (raw (.inr error)) () Empty.elim
  | ⟨event :: rest, result⟩ =>
      .request (raw (.inl event)) () (fun _ => ⟨rest, result⟩)

def listDriver (expectedList : Error) :
    FoldTraversal.Driver n (signature Event Error) (Value F) (Value F) (Option (List (Value F))) where
  start
    | .list values => some values
    | _ => none
  observe
    | none => .request (raw (.inr expectedList)) () Empty.elim
    | some [] => .done
    | some (item :: rest) => .yield item (some rest)

def engine (source : Source → Logged Event Error (Value F))
    (convert : Conversion → Value F → Value F) (expectedList : Error) :
    Engine n (signature Event Error) Source Conversion Unit (Value F)
      (Logged Event Error (Value F)) (Option (List (Value F))) where
  startSource := source
  source := sourceView
  convert := convert
  fold _ := listDriver expectedList

def liftPart : NominalListSpread.Part Source Conversion → Part Source Conversion Unit
  | .element code conversion => .element code conversion
  | .spread code => .spread code ()

def requests (events : List Event) : Row n (Event ⊕ Error) := events.map (fun event => raw (.inl event))

theorem source_trace_prefix (events : List Event) (value : Value F) :
    Prefix (sourceView (n := n) (Error := Error)) ⟨events, .ok value⟩ (requests events) ⟨[], .ok value⟩ := by
  induction events with
  | nil => exact .refl
  | cons event rest ih =>
      exact .cons (Step.answer (process := sourceView) (state := ⟨event :: rest, .ok value⟩)
        (payload := ()) (resume := fun _ => ⟨rest, .ok value⟩) rfl ()) ih

theorem source_result_prefix (logged : Logged Event Error (Value F))
    (returned : logged.result = .ok value) :
    Prefix (sourceView (n := n)) logged (requests logged.trace) ⟨[], .ok value⟩ := by
  cases logged with
  | mk trace result =>
      simp only at returned
      subst result
      exact source_trace_prefix trace value

theorem list_traversal (expectedList : Error) (values : List (Value F)) :
    FoldTraversal.Prefix (listDriver (n := n) (Event := Event) expectedList).observe
      (some values) values [] (some []) := by
  induction values with
  | nil => exact .refl
  | cons item rest ih =>
      exact .cons (FoldTraversal.Step.yield (protocol := (listDriver expectedList).observe) rfl) ih

/-- This is the very same finite cursor used by the existing list Fold/Index
view and by its unlabelled-for adapter. -/
theorem list_driver_cursor (expectedList : Error) (values : List (Value F)) :
    (listDriver (n := n) (Event := Event) expectedList).observe (some values) =
      match NominalListViews.nextItem values with
      | none => .done
      | some (item, rest) => .yield item (some rest) := by
  cases values <;> rfl

theorem part_meaning (source : Source → Logged Event Error (Value F))
    (convert : Conversion → Value F → Value F) (expectedList : Error)
    (returned : (source part.source).result = .ok value)
    (meaning : NominalListSpread.PartMeaning convert part value chunk) :
    PartMeaning (engine (n := n) source convert expectedList) (liftPart part) chunk
      (requests (source part.source).trace) := by
  cases meaning with
  | element =>
      exact .element (source_result_prefix _ returned) rfl
  | spread =>
      simpa [engine, liftPart, NominalListSpread.Part.source] using
        PartMeaning.spread (engine := engine (n := n) source convert expectedList)
        (dictionary := ()) (source_result_prefix _ returned) rfl (list_traversal expectedList _) rfl

theorem meaning (source : Source → Logged Event Error (Value F))
    (convert : Conversion → Value F → Value F) (expectedList : Error)
    (finiteMeaning : NominalListSpread.Meaning source convert parts chunks) :
    Meaning (engine (n := n) source convert expectedList) (parts.map liftPart) chunks.flatten
      (requests (NominalListSpread.sourceTrace source parts)) := by
  induction finiteMeaning with
  | nil => exact .nil
  | cons returned expanded tail ih =>
      simpa only [List.map_cons, List.flatten_cons, NominalListSpread.sourceTrace, List.flatMap_cons,
        requests, List.map_append] using Meaning.cons (part_meaning source convert expectedList returned expanded) ih

theorem finite_run_correspondence (source : Source → Logged Event Error (Value F))
    (convert : Conversion → Value F → Value F) (expectedList : Error)
    (finiteMeaning : NominalListSpread.Meaning source convert parts chunks) :
    NominalListSpread.run source convert expectedList parts =
      ⟨NominalListSpread.sourceTrace source parts, .ok chunks.flatten⟩ ∧
    Prefix (engine (n := n) source convert expectedList).observe (start (parts.map liftPart))
      (requests (NominalListSpread.sourceTrace source parts)) ⟨chunks.flatten, .ready []⟩ ∧
    (engine (n := n) source convert expectedList).observe ⟨chunks.flatten, .ready []⟩ = .value chunks.flatten :=
  ⟨NominalListSpread.meaning_evaluates source convert expectedList finiteMeaning,
    meaning_returns (meaning source convert expectedList finiteMeaning)⟩

end Yulang.FoldListSpreadFinite
