import Yulang.RoleEvidence
import Yulang.QualifiedExamples

/-!
# Rigid handler dictionaries in the actual signed structural model

The same arm resumes its abstract payload after using Add. It is accepted with
the signature's Add dictionary and rejected without it. The negative result is
universal in the output and in the operation-local type instantiation; it is
not a test that simply assigns the local variable a convenient concrete type.
-/

namespace Yulang.RoleEvidenceExamples

open Inference (Model Comp CompTerm TyTerm)
open RoleConstraints QualifiedInference RoleEvidence

abbrev Key := EffectInference.SigKey Nat Nat Nat
abbrev model := SignedStructural.model 1 Key
def key : Key := ⟨0, 0, []⟩
abbrev algebra := RowInference.signedAlgebra 1 Key
abbrev view := SignedStructural.rowView 1 Key

def noGlobal (decode : model.Ty → Roles.Term) : Theory model := resolvingTheory decode []

theorem no_global_evidence (decode : model.Ty → Roles.Term) (goal : Predicate model.Ty) :
    ¬ noGlobal decode goal := empty_resolver_has_no_evidence _

def signature : RoleEvidence.Signature Empty 1 Nat Nat Nat where
  operation := {
    key := key
    input := .var (.inr 0)
    output := .var (.inr 0)
  }
  requirements := [QualifiedExamples.addGoal (.var (.inr 0))]

def missingSignature : RoleEvidence.Signature Empty 1 Nat Nat Nat :=
  { signature with requirements := [] }

def operationBody : QualifiedInference.Expr :=
  .app (.var 1) (.app (.app (.method 0) (.var 0)) (.var 0))

theorem uses_dictionary_and_resumes (decode : model.Ty → Roles.Term) (t : model.Ty) :
    QualifiedInference.Typing model QualifiedExamples.methods
      (WithEvidence (noGlobal decode) [⟨0, [t]⟩])
      (RoleEvidence.semanticArmEnvironment model [] (Comp.pure model (.base .unit)) t t)
      operationBody (Comp.pure model (.base .unit)) := by
  apply QualifiedInference.Typing.app (a := Comp.pure model t)
    (b := Comp.pure model (.base .unit)) (ef := [])
  · exact .var rfl (.mono ⟨.refl _, SignedStructural.row_refl _⟩)
  · apply QualifiedInference.Typing.app (a := Comp.pure model t) (b := Comp.pure model t) (ef := [])
    · apply QualifiedInference.Typing.app (a := Comp.pure model t)
        (b := Comp.pure model (Comp.arrow model (Comp.pure model t) (Comp.pure model t))) (ef := [])
      · apply QualifiedInference.Typing.method (fun _ => t)
        · simp [QualifiedExamples.methods, QualifiedExamples.addMethod, QualifiedExamples.addGoal,
            typeEnv, Goal.eval, Predicate.map, TyTerm.eval, Comp.pure, Satisfies, WithEvidence]
        · exact ⟨.refl _, SignedStructural.row_refl _⟩
      · exact .var rfl (.mono ⟨.refl _, SignedStructural.row_refl _⟩)
      · exact ⟨.refl _, SignedStructural.row_refl _⟩
    · exact .var rfl (.mono ⟨.refl _, SignedStructural.row_refl _⟩)
    · exact ⟨.refl _, SignedStructural.row_refl _⟩
  · exact ⟨.refl _, SignedStructural.row_refl _⟩

/-- All local types are checked; none is unified with a convenient concrete type. -/
theorem generated_handler_uses_only_signature_dictionary (decode : model.Ty → Roles.Term) :
    (RoleEvidence.handlerConstraints QualifiedExamples.methods [] signature
      (.lit .unit) (.var 0) operationBody (CompTerm.pure (.base .unit))).Holds
        view (noGlobal decode) Empty.elim := by
  apply (RoleEvidence.handler_constraints_exact algebra view QualifiedExamples.methods
    (noGlobal decode) [] [] Empty.elim (fun theory => QualifiedInference.EnvRel.nil model theory Empty.elim)
    signature (.lit .unit) (.var 0) operationBody _).mpr
  apply RoleEvidence.HandlerTyping.intro
    (input := Comp.pure model (.base .unit)) (returned := Comp.pure model (.base .unit))
  · exact .lit ⟨.refl _, SignedStructural.row_refl _⟩
  · exact .var rfl (.mono ⟨.refl _, SignedStructural.row_refl _⟩)
  · intro ι
    refine ⟨Comp.pure model (.base .unit), uses_dictionary_and_resumes decode (ι 0), ?_, ?_⟩
    · exact .unionElim (.refl _) (.refl _)
    · exact SignedStructural.row_refl []

theorem method_without_evidence_rejected (decode : model.Ty → Roles.Term)
    (Γ : List (QualifiedInference.Binding model)) (out : Comp model) :
    ¬ QualifiedInference.Typing model QualifiedExamples.methods (noGlobal decode) Γ (.method 0) out := by
  intro h
  cases h with
  | method ι requirements _ =>
    change Fin 1 → model.Ty at ι
    change Satisfies (noGlobal decode) [⟨0, [ι 0]⟩] at requirements
    exact no_global_evidence decode _ (requirements ⟨0, [ι 0]⟩ (by simp))

theorem body_without_evidence_rejected (decode : model.Ty → Roles.Term)
    (Γ : List (QualifiedInference.Binding model)) (out : Comp model) :
    ¬ QualifiedInference.Typing model QualifiedExamples.methods (noGlobal decode) Γ operationBody out := by
  intro h
  cases h with
  | app _ argument _ =>
    cases argument with
    | app function _ _ =>
      cases function with
      | app method _ _ => exact method_without_evidence_rejected decode _ _ method

/-- Removing the signature's dictionary rejects the actual payload method use
for every result type/row expressible in the outer interface. -/
theorem generated_handler_without_evidence_rejected (decode : model.Ty → Roles.Term)
    (out : CompTerm Empty) :
    ¬ (RoleEvidence.handlerConstraints QualifiedExamples.methods [] missingSignature
      (.lit .unit) (.var 0) operationBody out).Holds view (noGlobal decode) Empty.elim := by
  intro h
  have typed := (RoleEvidence.handler_constraints_exact algebra view QualifiedExamples.methods
    (noGlobal decode) [] [] Empty.elim (fun theory => QualifiedInference.EnvRel.nil model theory Empty.elim)
    missingSignature (.lit .unit) (.var 0) operationBody out).mp h
  cases typed with
  | intro _ _ arms =>
    obtain ⟨operated, arm, _, _⟩ := arms (fun _ => .base .int)
    have emptyEvidence : WithEvidence (noGlobal decode) [] = noGlobal decode := by
      funext goal
      exact propext (by simp [WithEvidence])
    change QualifiedInference.Typing model QualifiedExamples.methods (WithEvidence (noGlobal decode) [])
      _ operationBody operated at arm
    rw [emptyEvidence] at arm
    exact body_without_evidence_rejected decode _ _ arm

/-- At a call, the same signature does not supply its own evidence. -/
theorem generated_request_without_evidence_rejected (decode : model.Ty → Roles.Term)
    (payload : QualifiedInference.Expr) (out : CompTerm Empty) :
    ¬ (RoleEvidence.requestConstraints QualifiedExamples.methods [] signature payload out).Holds
      view (noGlobal decode) Empty.elim := by
  intro h
  have typed := (RoleEvidence.request_constraints_exact algebra view QualifiedExamples.methods
    (noGlobal decode) [] [] Empty.elim (QualifiedInference.EnvRel.nil model _ _)
    signature payload out).mp h
  cases typed with
  | intro ι requirements _ =>
    change Satisfies (noGlobal decode) [⟨0, [ι 0]⟩] at requirements
    exact no_global_evidence decode _ (requirements ⟨0, [ι 0]⟩ (by simp))

end Yulang.RoleEvidenceExamples
