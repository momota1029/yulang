import Yulang.CaseDataTerms

/-!
# Nominal constructors with evaluated payloads

Resolved type 10 / constructor 0 models a struct, while type 20 / constructor 1
models an enum constructor. These identities are examples, not declarations or
an invented nominal registry. The source pass must validate declarations,
payload types, defaults and cast boundaries before emitting this syntax.

The payloads below are expressions: the struct evaluates a record with a
computed field, and the enum evaluates a let-bound variable. The list example
uses the existing nil/cons constructors and a computed element. Independent
typing gives evaluation safety; separate equalities expose the exact values
and visits, including the otherwise unused component of a computed pair.
-/

namespace Yulang.NominalDataConstructionExamples

open CaseValues CaseDataTerms LiteralValues EvaluationTrace

def intCode (integer : Int) : Expr Empty := .value (.literal (.int integer))

private theorem record_exact {types : List (Nat × Ty F)} {name : Nat}
    {head tail : Expr F} {value : Value F} {fields : Bindings F}
    (headTyped : Typing types head (Ty.exact value))
    (tailTyped : Typing types tail (Ty.exact (.record fields))) :
    Typing types (.record name head tail) (Ty.exact (.record (insert name value fields))) := by
  apply Typing.widen (Typing.record headTyped tailTyped ?_) ?_
  · intro actual same
    cases same
    trivial
  · intro actual constructed
    obtain ⟨headValue, restFields, headValid, tailValid, same⟩ := constructed
    change headValue = value at headValid
    change Value.record restFields = .record fields at tailValid
    have fieldsSame : restFields = fields := Value.record.inj tailValid
    subst headValue
    subst restFields
    exact same

private theorem cons_exact {types : List (Nat × Ty F)}
    {head tail : Expr F} {value : Value F} {values : List (Value F)}
    (headTyped : Typing types head (Ty.exact value))
    (tailTyped : Typing types tail (Ty.exact (.list values))) :
    Typing types (.cons head tail) (Ty.exact (.list (value :: values))) := by
  apply Typing.widen (Typing.cons headTyped tailTyped ?_) ?_
  · intro actual same
    cases same
    intro item member
    trivial
  · intro actual constructed
    obtain ⟨headValue, restValues, headValid, tailValid, same⟩ := constructed
    change headValue = value at headValid
    change Value.list restValues = .list values at tailValid
    have valuesSame : restValues = values := Value.list.inj tailValid
    subst headValue
    subst restValues
    exact same

def coordinate (first unused : Int) : Expr Empty :=
  .fst (.pair (intCode first) (intCode unused))

def pointTail (y : Int) : Expr Empty := .record 1 (intCode y) .emptyRecord

def pointPayload (x y unused : Int) : Expr Empty :=
  .record 0 (coordinate x unused) (pointTail y)

def point (x y unused : Int) : Expr Empty := .nominal 10 0 (pointPayload x y unused)

def pointPayloadValue (x y : Int) : Value Empty :=
  .record [(0, .literal (.int x)), (1, .literal (.int y))]

theorem pointPayload_typed (x y unused : Int) :
    Typing [] (pointPayload x y unused) (Ty.exact (pointPayloadValue x y)) :=
  record_exact (.fst (.pair .value .value)) (record_exact .value .emptyRecord)

theorem point_typed (x y unused : Int) :
    Typing [] (point x y unused) (Ty.nominal 10 0 (Ty.exact (pointPayloadValue x y))) :=
  .nominal (pointPayload_typed x y unused)

theorem point_evaluates_from_typing (x y unused : Int) :
    ∃ value, (eval [] (point x y unused)).result = .ok value ∧
      Ty.nominal 10 0 (Ty.exact (pointPayloadValue x y)) value :=
  typing_evaluates (point_typed x y unused) [] .nil

/-- The payload's record and both pair operands are evaluated before the
completed nominal value is returned; the unused operand's visit is retained. -/
theorem point_written_order (x y unused : Int) :
    eval [] (point x y unused) =
      ⟨[.source (point x y unused), .source (pointPayload x y unused),
        .source (coordinate x unused), .source (.pair (intCode x) (intCode unused)),
        .source (intCode x), .source (intCode unused),
        .source (pointTail y), .source (intCode y), .source .emptyRecord],
       .ok (.nominal 10 0 (pointPayloadValue x y))⟩ := rfl

def justPayload (integer : Int) : Expr Empty := .letE 4 (intCode integer) (.var 4)

def justValue (integer : Int) : Expr Empty := .nominal 20 1 (justPayload integer)

theorem just_typed (integer : Int) :
    Typing [] (justValue integer) (Ty.nominal 20 1 (Ty.exact (.literal (.int integer)))) :=
  .nominal (.letE .value (.var rfl))

theorem just_evaluates_from_typing (integer : Int) :
    ∃ value, (eval [] (justValue integer)).result = .ok value ∧
      Ty.nominal 20 1 (Ty.exact (.literal (.int integer))) value :=
  typing_evaluates (just_typed integer) [] .nil

theorem just_written_order (integer : Int) :
    eval [] (justValue integer) =
      ⟨[.source (justValue integer), .source (justPayload integer),
        .source (intCode integer), .source (.var 4)],
       .ok (.nominal 20 1 (.literal (.int integer)))⟩ := rfl

def listBody (second : Int) : Expr Empty :=
  .cons (.var 4) (.cons (intCode second) .nil)

def listValue (first second : Int) : Expr Empty :=
  .letE 4 (intCode first) (listBody second)

theorem list_typed (first second : Int) :
    Typing [] (listValue first second)
      (Ty.exact (.list [.literal (.int first), .literal (.int second)])) :=
  .letE .value (cons_exact (.var rfl) (cons_exact .value .nil))

theorem list_evaluates_from_typing (first second : Int) :
    ∃ value, (eval [] (listValue first second)).result = .ok value ∧
      Ty.exact (.list [.literal (.int first), .literal (.int second)]) value :=
  typing_evaluates (list_typed first second) [] .nil

theorem list_written_order (first second : Int) :
    eval [] (listValue first second) =
      ⟨[.source (listValue first second), .source (intCode first), .source (listBody second),
        .source (.var 4), .source (.cons (intCode second) .nil),
        .source (intCode second), .source .nil],
       .ok (.list [.literal (.int first), .literal (.int second)])⟩ := rfl

end Yulang.NominalDataConstructionExamples
