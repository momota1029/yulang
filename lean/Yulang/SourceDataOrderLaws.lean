import Yulang.SourceDataOrder

/-!
# Strict sequencing consequences for records, defaults and lets

The source equalities below follow from the independent evaluation rules.
They expose both the final stored value and all visits, so erasing a hidden
payload or retaining an existing field does not erase its evaluation.

The last section states the same observation-preservation laws for arbitrary
event logs. It is a reusable sequencing contract, not a claim that the current
data AST already evaluates effect requests or handlers.
-/

namespace Yulang.SourceDataOrderLaws

open Inference SourceDataRuntime SourceDataOrder
open EvaluationTrace (Logged)

theorem pair_sequence (first : Evaluates environment left leftTrace (.ok leftValue))
    (last : Evaluates environment right rightTrace (.ok rightValue)) :
    run environment (.pair left right) =
      ⟨.pair left right :: (leftTrace ++ rightTrace), .ok (.pair leftValue rightValue)⟩ :=
  (Evaluates.binaryValues .pair first last).executable

theorem record_sequence (label : Nat)
    (head : Evaluates environment first firstTrace (.ok firstValue))
    (tail : Evaluates environment rest restTrace (.ok (.record fields))) :
    run environment (.record label first rest) =
      ⟨.record label first rest :: (firstTrace ++ restTrace),
        .ok (.record (Fields.insert label firstValue fields))⟩ :=
  (Evaluates.binaryValues (.record label) head tail).executable

/-- A shadowed field contributes its complete evaluation trace even though
its stored payload disappears. The remaining spread is evaluated afterwards. -/
theorem shadowed_field_keeps_visits (label : Nat)
    (head : Evaluates environment first firstTrace (.ok firstValue))
    (hidden : Evaluates environment discarded discardedTrace (.ok discardedValue))
    (tail : Evaluates environment rest restTrace (.ok (.record fields))) :
    run environment (.record label first (.record label discarded rest)) =
      ⟨.record label first (.record label discarded rest) ::
        (firstTrace ++ .record label discarded rest :: (discardedTrace ++ restTrace)),
        .ok (.record (Fields.insert label firstValue fields))⟩ := by
  have inner := Evaluates.binaryValues (.record label) hidden tail
  have outer := (Evaluates.binaryValues (.record label) head inner).executable
  simpa only [Binary.expr, Binary.apply, Fields.insert_shadow] using outer

/-- A failing hidden expression is observable: the record fails there and
the later spread is not visited. No premise about that spread is needed. -/
theorem shadowed_field_error (label : Nat) (rest : Expr)
    (head : Evaluates environment first firstTrace (.ok firstValue))
    (hidden : Evaluates environment discarded discardedTrace (.error error)) :
    run environment (.record label first (.record label discarded rest)) =
      ⟨.record label first (.record label discarded rest) ::
        (firstTrace ++ .record label discarded rest :: discardedTrace), .error error⟩ :=
  (Evaluates.binaryLastError (.record label) head
    (Evaluates.binaryFirstError (.record label) rest hidden)).executable

theorem default_sequence (label : Nat)
    (base : Evaluates environment baseExpr baseTrace (.ok (.record fields)))
    (fallback : Evaluates environment fallbackExpr fallbackTrace (.ok fallbackValue)) :
    run environment (.recordDefault label baseExpr fallbackExpr) =
      ⟨.recordDefault label baseExpr fallbackExpr :: (baseTrace ++ fallbackTrace),
        .ok (.record (Fields.insertDefault label fallbackValue fields))⟩ :=
  (Evaluates.binaryValues (.recordDefault label) base fallback).executable

/-- The existing field wins only after the fallback expression has run. -/
theorem default_present_keeps_fallback_visits (label : Nat) (existing : Value)
    (base : Evaluates environment baseExpr baseTrace (.ok (.record fields)))
    (fallback : Evaluates environment fallbackExpr fallbackTrace (.ok fallbackValue))
    (present : Fields.lookup label fields = some existing) :
    run environment (.recordDefault label baseExpr fallbackExpr) =
      ⟨.recordDefault label baseExpr fallbackExpr :: (baseTrace ++ fallbackTrace), .ok (.record fields)⟩ := by
  simpa only [Fields.insertDefault_present label fallbackValue existing fields present] using
    default_sequence label base fallback

theorem default_absent_appends (label : Nat)
    (base : Evaluates environment baseExpr baseTrace (.ok (.record fields)))
    (fallback : Evaluates environment fallbackExpr fallbackTrace (.ok fallbackValue))
    (absent : Fields.lookup label fields = none) :
    run environment (.recordDefault label baseExpr fallbackExpr) =
      ⟨.recordDefault label baseExpr fallbackExpr :: (baseTrace ++ fallbackTrace),
        .ok (.record (fields ++ [(label, fallbackValue)]))⟩ := by
  simpa only [Fields.insertDefault_absent label fallbackValue fields absent] using
    default_sequence label base fallback

/-- A fallback failure propagates regardless of whether the base already
has the field. It also precedes a later record-shape check of the base value. -/
theorem default_fallback_error (label : Nat)
    (base : Evaluates environment baseExpr baseTrace (.ok baseValue))
    (fallback : Evaluates environment fallbackExpr fallbackTrace (.error error)) :
    run environment (.recordDefault label baseExpr fallbackExpr) =
      ⟨.recordDefault label baseExpr fallbackExpr :: (baseTrace ++ fallbackTrace), .error error⟩ :=
  (Evaluates.binaryLastError (.recordDefault label) base fallback).executable

/-- A failure in the earlier spread stops before the fallback is entered. -/
theorem default_base_error (label : Nat) (fallbackExpr : Expr)
    (base : Evaluates environment baseExpr baseTrace (.error error)) :
    run environment (.recordDefault label baseExpr fallbackExpr) =
      ⟨.recordDefault label baseExpr fallbackExpr :: baseTrace, .error error⟩ :=
  (Evaluates.binaryFirstError (.recordDefault label) fallbackExpr base).executable

theorem unused_let_keeps_rhs_visits (base : Base)
    (definition : Evaluates environment expression definitionTrace (.ok value)) :
    run environment (.letE expression (.lit base)) =
      ⟨.letE expression (.lit base) :: (definitionTrace ++ [.lit base]), .ok (.base base)⟩ :=
  (Evaluates.letValue definition (Evaluates.literal base)).executable

theorem unused_let_rhs_error (base : Base)
    (definition : Evaluates environment expression definitionTrace (.error error)) :
    run environment (.letE expression (.lit base)) =
      ⟨.letE expression (.lit base) :: definitionTrace, .error error⟩ :=
  (Evaluates.letError (.lit base) definition).executable

/-- Two reads use the stored value. The strict definition's visits occur
once, before both reads, rather than being replayed on either variable lookup. -/
theorem let_two_reads_evaluates_rhs_once
    (definition : Evaluates environment expression definitionTrace (.ok value)) :
    run environment (.letE expression (.pair (.var 0) (.var 0))) =
      ⟨.letE expression (.pair (.var 0) (.var 0)) ::
        (definitionTrace ++ [.pair (.var 0) (.var 0), .var 0, .var 0]), .ok (.pair value value)⟩ :=
  (Evaluates.letValue definition (Evaluates.binaryValues .pair
    (Evaluates.bound rfl) (Evaluates.bound rfl))).executable

/-! ## Reusable observation laws for an effectful sequencing extension -/

universe u

theorem default_present_keeps_observations {Event : Type u}
    (baseTrace fallbackTrace : List Event) (label : Nat)
    (fields : List (Nat × Value)) (fallback existing : Value)
    (present : Fields.lookup label fields = some existing) :
    Logged.sequence (Error := Error) ⟨baseTrace, .ok (.record fields)⟩
      (fun _ => ⟨fallbackTrace, .ok fallback⟩) (Binary.recordDefault label).apply =
        ⟨baseTrace ++ fallbackTrace, .ok (.record fields)⟩ := by
  simp only [Logged.sequence_values, Binary.apply,
    Fields.insertDefault_present label fallback existing fields present]

theorem shadowed_field_keeps_observations {Event : Type u}
    (firstTrace hiddenTrace restTrace : List Event) (label : Nat)
    (first hidden : Value) (fields : List (Nat × Value)) :
    Logged.sequence (Error := Error) ⟨firstTrace, .ok first⟩
      (fun _ => Logged.sequence ⟨hiddenTrace, .ok hidden⟩
        (fun _ => ⟨restTrace, .ok (.record fields)⟩) (Binary.record label).apply)
      (Binary.record label).apply =
        ⟨firstTrace ++ hiddenTrace ++ restTrace, .ok (.record (Fields.insert label first fields))⟩ := by
  simp only [Logged.sequence_values, Binary.apply, Fields.insert_shadow, List.append_assoc]

end Yulang.SourceDataOrderLaws
