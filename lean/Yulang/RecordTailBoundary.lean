import Yulang.Inference
import Yulang.StructuralDecisions

/-!
# A boundary of normalization to a known record spine

The current reference algebra distinguishes a record whose tail is syntactically
`emptyRecord` from one whose tail is `emptyRecord | bottom`. Although those tails
are mutual subtypes, the latter record is not a syntactic `IsRecord` spine and
cannot use the structural record rule.

This is observable in the existing inference judgment: the same closed record
literal has both result types, and both are instances of its generated principal
formula. No proper record spine has exactly all its typings as upward instances.
Consequently, replacing the tail by an equivalent proper spine does not preserve
the existing full instance set. This does not contradict principality of the
constraint formula, or prove that a more general solver is impossible.

The example uses a one-element row model to isolate the value-type issue. It
changes neither `Typing` nor `Subtype`, and assumes no proposed repair of record
semantics. Negative subtyping results follow from the existing cut-elimination
theorem; the executable ground checker also rejects all three comparisons.
-/

namespace Yulang.RecordTailBoundary

open Inference StructuralBase

abbrev rowLe (_ _ : Unit) : Prop := True
abbrev rowCheck (_ _ : Unit) : Bool := true
abbrev pureModel := StructuralBase.model Unit () (fun _ _ => ()) rowLe
abbrev emptyInput : Empty → Comp pureModel := Empty.elim

abbrev equivalentTail : Ty Unit := .union .emptyRecord .bottom
abbrev properRecord : Ty Unit := .record 0 (.base .int) .emptyRecord
abbrev rawTailRecord : Ty Unit := .record 0 (.base .int) equivalentTail
abbrev recordLiteral : Expr := .record 0 (.lit .int) .emptyRecord

theorem empty_le_tail : Subtype rowLe .emptyRecord equivalentTail :=
  .unionLeft _ _

theorem tail_le_empty : Subtype rowLe equivalentTail .emptyRecord :=
  .unionElim (.refl _) (.bottom _)

theorem tail_not_record_spine : ¬ IsRecord equivalentTail := by
  intro shape
  cases shape

theorem proper_is_record_spine : IsRecord properRecord := .field .empty

theorem raw_tail_not_record_spine : ¬ IsRecord rawTailRecord := by
  intro shape
  cases shape with
  | field rest => exact tail_not_record_spine rest

theorem literal_proper : Typing pureModel [] recordLiteral (properRecord, ()) := by
  apply Typing.record (m := pureModel) (a := (Ty.base .int, ())) (b := (Ty.emptyRecord, ()))
  · exact .lit ⟨.refl _, trivial⟩
  · exact .emptyRecord ⟨.refl _, trivial⟩
  · exact .refl _
  · exact ⟨.refl _, trivial⟩

theorem literal_raw_tail : Typing pureModel [] recordLiteral (rawTailRecord, ()) := by
  apply Typing.record (m := pureModel) (a := (Ty.base .int, ())) (b := (equivalentTail, ()))
  · exact .lit ⟨.refl _, trivial⟩
  · exact .emptyRecord ⟨empty_le_tail, trivial⟩
  · exact tail_le_empty
  · exact ⟨.refl _, trivial⟩

theorem principal_raw_tail :
    (principal ([] : SchemeEnv Empty) recordLiteral).Holds pureModel
      (extend emptyInput (rawTailRecord, ())) := by
  exact (principal_exact pureModel recordLiteral [] [] emptyInput
    (EnvRel.nil pureModel emptyInput) (rawTailRecord, ())).mpr literal_raw_tail

theorem principal_proper :
    (principal ([] : SchemeEnv Empty) recordLiteral).Holds pureModel
      (extend emptyInput (properRecord, ())) := by
  exact (principal_exact pureModel recordLiteral [] [] emptyInput
    (EnvRel.nil pureModel emptyInput) (properRecord, ())).mpr literal_proper

theorem no_record_spine_le_raw_tail {candidate : Ty Unit}
    (shape : IsRecord candidate) : ¬ Subtype rowLe candidate rawTailRecord := by
  intro subtype
  have comparison := StructuralDecisions.Comparison.complete
    (leRow := rowLe) (fun _ _ => trivial) subtype
  cases shape with
  | empty =>
      cases comparison with
      | record _ target _ _ => exact raw_tail_not_record_spine target
  | field rest =>
      cases comparison with
      | refl => exact tail_not_record_spine rest
      | record _ target _ _ => exact raw_tail_not_record_spine target

theorem raw_tail_le_no_record_spine {candidate : Ty Unit}
    (shape : IsRecord candidate) : ¬ Subtype rowLe rawTailRecord candidate := by
  intro subtype
  have comparison := StructuralDecisions.Comparison.complete
    (leRow := rowLe) (fun _ _ => trivial) subtype
  cases shape with
  | empty =>
      cases comparison with
      | record source _ _ _ => exact raw_tail_not_record_spine source
  | field rest =>
      cases comparison with
      | refl => exact tail_not_record_spine rest
      | record source _ _ _ => exact raw_tail_not_record_spine source

theorem proper_not_raw_tail : ¬ Subtype rowLe properRecord rawTailRecord :=
  no_record_spine_le_raw_tail proper_is_record_spine

theorem raw_tail_not_proper : ¬ Subtype rowLe rawTailRecord properRecord :=
  raw_tail_le_no_record_spine proper_is_record_spine

theorem raw_tail_not_empty : ¬ Subtype rowLe rawTailRecord .emptyRecord :=
  raw_tail_le_no_record_spine .empty

theorem equivalent_tails_do_not_give_equivalent_records :
    (Subtype rowLe equivalentTail .emptyRecord ∧ Subtype rowLe .emptyRecord equivalentTail) ∧
      ¬ (Subtype rowLe rawTailRecord properRecord ∧ Subtype rowLe properRecord rawTailRecord) :=
  ⟨⟨tail_le_empty, empty_le_tail⟩, fun subtype => raw_tail_not_proper subtype.1⟩

theorem proper_record_loses_principal_instance :
    (principal ([] : SchemeEnv Empty) recordLiteral).Holds pureModel
      (extend emptyInput (rawTailRecord, ())) ∧
    ¬ Comp.le pureModel (properRecord, ()) (rawTailRecord, ()) :=
  ⟨principal_raw_tail, fun subtype => proper_not_raw_tail subtype.1⟩

theorem no_record_spine_represents_all_typings :
    ¬ ∃ candidate : Ty Unit, IsRecord candidate ∧
      (∀ result : Ty Unit, Typing pureModel [] recordLiteral (result, ()) ↔
        Subtype rowLe candidate result) := by
  rintro ⟨candidate, shape, represents⟩
  exact no_record_spine_le_raw_tail shape ((represents rawTailRecord).mp literal_raw_tail)

theorem no_record_spine_represents_principal :
    ¬ ∃ candidate : Ty Unit, IsRecord candidate ∧
      (∀ result : Ty Unit,
        (principal ([] : SchemeEnv Empty) recordLiteral).Holds pureModel
          (extend emptyInput (result, ())) ↔ Subtype rowLe candidate result) := by
  rintro ⟨candidate, shape, represents⟩
  exact no_record_spine_le_raw_tail shape ((represents rawTailRecord).mp principal_raw_tail)

theorem proper_to_raw_tail_rejected :
    StructuralDecisions.check rowCheck properRecord rawTailRecord = false := by decide +kernel

theorem raw_tail_to_proper_rejected :
    StructuralDecisions.check rowCheck rawTailRecord properRecord = false := by decide +kernel

theorem raw_tail_to_empty_rejected :
    StructuralDecisions.check rowCheck rawTailRecord .emptyRecord = false := by decide +kernel

end Yulang.RecordTailBoundary
