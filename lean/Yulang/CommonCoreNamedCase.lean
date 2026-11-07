import Yulang.CommonSolvedSource

/-!
# A single unguarded name-pattern case on the common carrier

`CasePatterns.Pattern.bind` produces one binding for the whole subject; its
name list is a singleton and Core arm elaboration puts that binding before
the surrounding context. The body therefore reads it at de Bruijn index zero.
It is a monomorphic local value, not a freshly generalized value-let scheme.

The lowering makes the subject syntactically computed without changing any
of its common typings: `fst (subject, unit)`. The outer let can consequently
use only the computed rule. Subjects, bodies, contexts, result types and rows
remain unrestricted. No general guard, default or multi-arm rule is asserted.
-/

namespace Yulang.CommonCoreNamedCase

open Core.PresenceGeneration
open Inference (Expr)

/-- A transparent computation that prevents value-let generalization. -/
def forceValue (subject : Expr) : Expr := .fst (.pair subject (.lit .unit))

/-- The named arm's body already uses de Bruijn index zero for its sole local
binder. The resolved name is provenance and does not change this lowering. -/
def caseName (subject body : Expr) : Expr := .letE (forceValue subject) body

/-- Independent common typing rule for one unguarded whole-value binder.
Subject evaluation contributes its row once; the bound value itself is pure. -/
inductive NamedCaseTyping (environment : List (Binding Common.model))
    (subject body : Expr) (result : Comp Common.model) : Prop where
  | bind {selected returned : Comp Common.model} :
      Typing Common.model environment subject selected →
      Typing Common.model (.mono (Comp.pure Common.model selected.1) :: environment) body returned →
      Comp.le Common.model (returned.1, Common.rowJoin selected.2 returned.2) result →
      NamedCaseTyping environment subject body result

@[simp] theorem forceValue_isValue (subject : Expr) : (forceValue subject).isValue = false := rfl

/-- Every context and every computation result, including arbitrary captured
schemes, regular common values and nonempty rows. The unit administrative
operand contributes no required effects and cannot change the subject type. -/
theorem forceValue_typing_exact (environment : List (Binding Common.model))
    (subject : Expr) (result : Comp Common.model) :
    Typing Common.model environment (forceValue subject) result ↔
      Typing Common.model environment subject result := by
  constructor
  · intro typed
    cases typed with
    | fst pairTyped projected =>
        cases pairTyped with
        | pair subjectTyped _ paired =>
            have components := (Common.common_pair_iff _ _ _ _).mp paired.1
            have rows := (Common.rowJoin_le_iff _ _ _).mp paired.2
            exact CommonPresenceSourceFamily.typing_subsume subjectTyped result
              ⟨Common.subtype_trans components.1 projected.1, Common.rowLe_trans rows.1 projected.2⟩
  · intro typed
    have unitTyped : Typing Common.model environment (.lit .unit)
        (Comp.pure Common.model (.base .unit)) :=
      .lit ⟨Common.subtype_refl _, Common.rowLe_refl _⟩
    have paired : Typing Common.model environment (.pair subject (.lit .unit))
        (Common.pair result.1 (.base .unit), result.2) :=
      .pair typed unitTyped
        ⟨Common.subtype_refl _,
          (Common.rowJoin_le_iff _ _ _).mpr ⟨Common.rowLe_refl _, Common.rowEmpty_le _⟩⟩
    exact .fst paired ⟨Common.subtype_refl _, Common.rowLe_refl _⟩

/-- Exactly the monomorphic arm rule. In particular, even a lambda or other
syntactic value used as the subject cannot select the value-let rule. -/
theorem caseName_typing_exact (environment : List (Binding Common.model))
    (subject body : Expr) (result : Comp Common.model) :
    Typing Common.model environment (caseName subject body) result ↔
      ∃ selected returned : Comp Common.model,
        Typing Common.model environment subject selected ∧
        Typing Common.model (.mono (Comp.pure Common.model selected.1) :: environment) body returned ∧
        Comp.le Common.model (returned.1, Common.rowJoin selected.2 returned.2) result := by
  rw [caseName, Typing.letComputed_iff Common.model environment (forceValue subject) body result
    (forceValue_isValue subject)]
  simp only [forceValue_typing_exact]
  rfl

theorem namedCaseTyping_iff (environment : List (Binding Common.model))
    (subject body : Expr) (result : Comp Common.model) :
    NamedCaseTyping environment subject body result ↔
      ∃ selected returned : Comp Common.model,
        Typing Common.model environment subject selected ∧
        Typing Common.model (.mono (Comp.pure Common.model selected.1) :: environment) body returned ∧
        Comp.le Common.model (returned.1, Common.rowJoin selected.2 returned.2) result := by
  constructor
  · intro typed
    cases typed with
    | bind selected body bounded => exact ⟨_, _, selected, body, bounded⟩
  · rintro ⟨_, _, selected, body, bounded⟩
    exact .bind selected body bounded

theorem lowering_exact (environment : List (Binding Common.model))
    (subject body : Expr) (result : Comp Common.model) :
    Typing Common.model environment (caseName subject body) result ↔
      NamedCaseTyping environment subject body result :=
  (caseName_typing_exact environment subject body result).trans
    (namedCaseTyping_iff environment subject body result).symm

/-- The existing finite generate/compile/worklist/row pipeline, applied to
the explicit non-generalizing lowering. Parameters remain its ordinary product. -/
def infer (subject body : Expr) : List CommonSolvedSource.Scheme :=
  CommonSolvedSource.inferSource (caseName subject body)

theorem principal (subject body : Expr) (result : Comp Common.model) :
    NamedCaseTyping [] subject body result ↔
      ∃ scheme ∈ infer subject body, ∃ parameters : scheme.Parameters,
        Comp.le Common.model (scheme.instantiate parameters) result :=
  (lowering_exact [] subject body result).symm.trans
    (CommonSolvedSource.source_principal (caseName subject body) result)

/-- Every returned scheme and every parameter assignment, with no residual,
support, success, row or type condition on those assignments. -/
theorem all_parameter_sound (subject body : Expr) (scheme : CommonSolvedSource.Scheme)
    (member : scheme ∈ infer subject body) (parameters : scheme.Parameters) :
    NamedCaseTyping [] subject body (scheme.instantiate parameters) :=
  (lowering_exact [] subject body _).mp
    (CommonSolvedSource.source_instantiates (caseName subject body) scheme member parameters)

theorem rejected_iff (subject body : Expr) :
    infer subject body = [] ↔ ¬ ∃ result, NamedCaseTyping [] subject body result := by
  rw [infer, CommonSolvedSource.source_empty_iff]
  simp only [lowering_exact]

end Yulang.CommonCoreNamedCase
