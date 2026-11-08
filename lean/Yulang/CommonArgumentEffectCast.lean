import Yulang.CommonCoreStrictApplication

/-!
# Explicit argument-effect conversion (spec 5.5c)

This is a kernel value-only-arrow conversion, not a translation of an omitted
source input row. Spec 5.5c says omission permits every incoming row; no equation
identifying source omission with `rowEmpty` is defined or proved here. The empty
row below describes the pure value passed after the existing strict lowering
has already evaluated the argument. The missing source-omission-to-kernel
elaboration bridge is recorded separately.

The independent conversion is separate from ordinary arrow subtyping. All rows
are Common occurrence predicates, including non-finite ones. Application below
is a soundness bridge to the existing strict lowering, not a new source insertion
algorithm or a completeness theorem for all strict applications.
-/
namespace Yulang.CommonArgumentEffectCast

open Common
open Core.PresenceGeneration

/-- Kernel value-only-arrow adapter, not a new constructor of `Common.Subtype`.
`rowEmpty` describes the post-force pure value interface, NOT an omitted source
input row. This judgment is not yet the full source spec-5.5c coercion judgment. -/
inductive ArgumentCast : Ty → Ty → Prop where
  | lift (argument result : Ty) (body incoming : Row) :
      ArgumentCast (arrow argument rowEmpty result body)
        (arrow argument incoming result (rowJoin body incoming))

/-- Auxiliary/exactness: all witnesses and both endpoint equalities are retained. -/
theorem argumentCast_iff (source target : Ty) :
    ArgumentCast source target ↔ ∃ argument result body incoming,
      source = arrow argument rowEmpty result body ∧
      target = arrow argument incoming result (rowJoin body incoming) := by
  constructor
  · intro converted
    cases converted with
    | lift argument result body incoming => exact ⟨argument, result, body, incoming, rfl, rfl⟩
  · rintro ⟨argument, result, body, incoming, rfl, rfl⟩
    exact .lift argument result body incoming

/-- Auxiliary: the existing standard arrow order deliberately rejects this
comparison whenever the incoming row has an occurrence. This is not a new
language rejection: explicit conversion supplies a different judgment. -/
theorem nonempty_cast_not_subtype (argument result : Ty) (body incoming : Row)
    (occurrence : Occurrence) (member : incoming occurrence) :
    ¬ Subtype (arrow argument rowEmpty result body)
      (arrow argument incoming result (rowJoin body incoming)) := by
  intro below
  have rows := ((common_arrow_iff argument argument result result rowEmpty incoming
    body (rowJoin body incoming)).mp below).2.1
  exact rows occurrence member

/-- Auxiliary: effect rows are sets, so their reported join order does not
change membership. This says nothing about operational request order. -/
theorem rowJoin_comm (first last : Row) : rowJoin first last = rowJoin last first := by
  funext occurrence
  exact propext or_comm

/-- Soundness: for arbitrary Common source environment and operands, an ordinary
kernel value-only function and an argument with incoming effects are accepted by the existing
strict lowering with those effects retained. No historical `.app` rule changes.
The premise explicitly contains `rowEmpty`; it does not infer that premise from
a source annotation whose input row is omitted. -/
theorem ordinary_application_preserved
    (environment : CommonCoreStrictApplication.Context) (function argument : Inference.Expr)
    (input output : Ty) (body incoming functionRow : Row)
    (functionTyped : Typing model environment function
      (arrow input rowEmpty output body, functionRow))
    (argumentTyped : Typing model environment argument (input, incoming)) :
    Typing model environment
      (CommonCoreStrictApplication.forceApplication function argument)
      (output, rowJoin functionRow (rowJoin body incoming)) := by
  apply CommonCoreStrictApplication.forceApplication_preserved
  refine .app (input := (input, rowEmpty)) (output := (output, body))
    (actual := (input, incoming)) functionTyped argumentTyped
    ⟨subtype_refl _, rowLe_refl _⟩ ?_
  refine ⟨subtype_refl _, ?_⟩
  intro occurrence member
  rcases member with funEffect | argEffect | bodyEffect
  · exact Or.inl funEffect
  · exact Or.inr (Or.inr argEffect)
  · exact Or.inr (Or.inl bodyEffect)

end Yulang.CommonArgumentEffectCast
