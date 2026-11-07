import Yulang.CommonNominalFullSourceSubsumption
import Yulang.CommonNominalFullConstructors

/-!
# The original unguarded name-case lowering over all nominal Common types

Subjects, bodies, rows and captured environments use the full new carrier.
The whole subject is bound monomorphically; the original administrative pair
prevents selecting a generalized value-let rule. General patterns remain B2.
-/

namespace Yulang.CommonNominalFullNamedCase

open Core.PresenceGeneration
open Inference (Expr)

/-- A transparent computation that prevents value-let generalization. -/
def forceValue (subject : Expr) : Expr := .fst (.pair subject (.lit .unit))

/-- The named arm's body already uses de Bruijn index zero for its sole local
binder. The resolved name is provenance and does not change this lowering. -/
def caseName (subject body : Expr) : Expr := .letE (forceValue subject) body

/-- Independent common typing rule for one unguarded whole-value binder.
Subject evaluation contributes its row once; the bound value itself is pure. -/
inductive NamedCaseTyping (environment : List (Binding CommonNominalFullCarrier.model))
    (subject body : Expr) (result : Comp CommonNominalFullCarrier.model) : Prop where
  | bind {selected returned : Comp CommonNominalFullCarrier.model} :
      Typing CommonNominalFullCarrier.model environment subject selected →
      Typing CommonNominalFullCarrier.model (.mono (Comp.pure CommonNominalFullCarrier.model selected.1) :: environment) body returned →
      Comp.le CommonNominalFullCarrier.model (returned.1, Common.rowJoin selected.2 returned.2) result →
      NamedCaseTyping environment subject body result

@[simp] theorem forceValue_isValue (subject : Expr) : (forceValue subject).isValue = false := rfl

/-- Every context and every computation result, including arbitrary captured
schemes, regular common values and nonempty rows. The unit administrative
operand contributes no required effects and cannot change the subject type. -/
theorem forceValue_typing_exact (environment : List (Binding CommonNominalFullCarrier.model))
    (subject : Expr) (result : Comp CommonNominalFullCarrier.model) :
    Typing CommonNominalFullCarrier.model environment (forceValue subject) result ↔
      Typing CommonNominalFullCarrier.model environment subject result := by
  constructor
  · intro typed
    cases typed with
    | fst pairTyped projected =>
        cases pairTyped with
        | pair subjectTyped _ paired =>
            have components := (CommonNominalFullCarrier.common_pair_iff _ _ _ _).mp paired.1
            have rows := (Common.rowJoin_le_iff _ _ _).mp paired.2
            exact CommonNominalFullSourceSubsumption.typing_subsume subjectTyped result
              ⟨CommonNominalFullCarrier.subtype_trans components.1 projected.1, Common.rowLe_trans rows.1 projected.2⟩
  · intro typed
    have unitTyped : Typing CommonNominalFullCarrier.model environment (.lit .unit)
        (Comp.pure CommonNominalFullCarrier.model (.base .unit)) :=
      .lit ⟨CommonNominalFullCarrier.subtype_refl _, Common.rowLe_refl _⟩
    have paired : Typing CommonNominalFullCarrier.model environment (.pair subject (.lit .unit))
        (CommonNominalFullCarrier.pair result.1 (.base .unit), result.2) :=
      .pair typed unitTyped
        ⟨CommonNominalFullCarrier.subtype_refl _,
          (Common.rowJoin_le_iff _ _ _).mpr ⟨Common.rowLe_refl _, Common.rowEmpty_le _⟩⟩
    exact .fst paired ⟨CommonNominalFullCarrier.subtype_refl _, Common.rowLe_refl _⟩

/-- Exactly the monomorphic arm rule. In particular, even a lambda or other
syntactic value used as the subject cannot select the value-let rule. -/
theorem caseName_typing_exact (environment : List (Binding CommonNominalFullCarrier.model))
    (subject body : Expr) (result : Comp CommonNominalFullCarrier.model) :
    Typing CommonNominalFullCarrier.model environment (caseName subject body) result ↔
      ∃ selected returned : Comp CommonNominalFullCarrier.model,
        Typing CommonNominalFullCarrier.model environment subject selected ∧
        Typing CommonNominalFullCarrier.model (.mono (Comp.pure CommonNominalFullCarrier.model selected.1) :: environment) body returned ∧
        Comp.le CommonNominalFullCarrier.model (returned.1, Common.rowJoin selected.2 returned.2) result := by
  rw [caseName, Typing.letComputed_iff CommonNominalFullCarrier.model environment (forceValue subject) body result
    (forceValue_isValue subject)]
  simp only [forceValue_typing_exact]
  rfl

theorem namedCaseTyping_iff (environment : List (Binding CommonNominalFullCarrier.model))
    (subject body : Expr) (result : Comp CommonNominalFullCarrier.model) :
    NamedCaseTyping environment subject body result ↔
      ∃ selected returned : Comp CommonNominalFullCarrier.model,
        Typing CommonNominalFullCarrier.model environment subject selected ∧
        Typing CommonNominalFullCarrier.model (.mono (Comp.pure CommonNominalFullCarrier.model selected.1) :: environment) body returned ∧
        Comp.le CommonNominalFullCarrier.model (returned.1, Common.rowJoin selected.2 returned.2) result := by
  constructor
  · intro typed
    cases typed with
    | bind selected body bounded => exact ⟨_, _, selected, body, bounded⟩
  · rintro ⟨_, _, selected, body, bounded⟩
    exact .bind selected body bounded

theorem lowering_exact (environment : List (Binding CommonNominalFullCarrier.model))
    (subject body : Expr) (result : Comp CommonNominalFullCarrier.model) :
    Typing CommonNominalFullCarrier.model environment (caseName subject body) result ↔
      NamedCaseTyping environment subject body result :=
  (caseName_typing_exact environment subject body result).trans
    (namedCaseTyping_iff environment subject body result).symm

end Yulang.CommonNominalFullNamedCase
