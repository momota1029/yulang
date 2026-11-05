import Yulang.OperationalCorrespondence
import Yulang.OperationalTypingExamples

/-!
# Concrete solutions of the operational principal formula

The recursive generator's solution premise is inhabited for an actual request
and for an application whose lambda body handles a permitted computation
argument. The same request formula has no solution with an empty row, for any
result value type. The effect bounds below use the principal-formula entry point,
independently of the executable checker's successful examples.

As in `OperationalCorrespondence`, atoms use the homogeneous `unit` carrier and
all runtime shapes are already resolved. The erasure forgets input annotations;
these examples do not claim equality of the checker's and generator's accepted
sets or insert source-language hygiene wrappers.
-/

namespace Yulang.OperationalCorrespondenceExamples

open Directed OperationalTyping OperationalCorrespondence

def pureUnit : CoreComp 1 Nat := (.base .unit, [])
def effectUnit : CoreComp 1 Nat := (.base .unit, [raw 0])

def request : Expr 1 Nat Nat [] .atom := .request 0 (.lit 2)

theorem request_typing : CoreTyping [] (erase request) effectUnit := by
  apply RecursiveEffects.Typing.request (er := [])
  · exact .lit ⟨.refl _, SignedStructural.row_refl _⟩
  · exact .refl _
  · exact SignedStructural.row_refl _

theorem request_solution :
    (principal request).Holds (Model 1 Nat) (SignedStructural.rowView 1 Nat)
      (Inference.extend Empty.elim effectUnit) := by
  apply (RecursiveEffects.principal_exact (Model 1 Nat) (SignedStructural.rowView 1 Nat)
    (signatures 1 Nat) (erase request) (signatureTerms Nat Empty) [] [] Empty.elim
    (RecursiveEffects.EnvRel.nil _ _ _ _) (fun _ => rfl) effectUnit).mpr
  exact request_typing

theorem request_bound_from_solution :
    Computation.BoundedBy [raw 0] (eval Env.nil request) :=
  principal_effect_bound request effectUnit request_solution

/-- The actual request rules out every empty-row solution, not just one type. -/
theorem request_empty_rejected (result : CoreType 1 Nat) :
    ¬ (principal request).Holds (Model 1 Nat) (SignedStructural.rowView 1 Nat)
      (Inference.extend Empty.elim (result, [])) := by
  intro solution
  have bounded := principal_effect_bound request (result, []) solution
  exact List.not_mem_nil bounded.1

theorem handledArgument_typing :
    CoreTyping [] (erase OperationalTypingExamples.handledArgument) pureUnit := by
  apply RecursiveEffects.Typing.app (a := effectUnit) (b := pureUnit) (ef := [])
  · apply RecursiveEffects.Typing.lam (a := effectUnit) (b := pureUnit)
    · apply RecursiveEffects.Typing.handler
        (input := effectUnit) (returned := pureUnit) (operated := pureUnit)
      · apply RecursiveEffects.Typing.boundary (input := effectUnit)
        · exact .var rfl (.mono ⟨.refl _, SignedStructural.row_refl _⟩)
        · exact .refl _
        · intro occurrence member
          change List.Mem occurrence ([raw 0].map (protect 0 allowAll)) at member
          change List.Mem occurrence [raw 0]
          simpa only [List.map_cons, List.map_nil, protect, glob_has_no_transport] using member
      · exact .var rfl (.mono ⟨.refl _, SignedStructural.row_refl _⟩)
      · exact .lit ⟨.refl _, SignedStructural.row_refl _⟩
      · exact .unionElim (.refl _) (.refl _)
      · intro occurrence member
        change List.Mem occurrence [] at member
        exact member
    · exact ⟨.refl _, SignedStructural.row_refl _⟩
  · exact request_typing
  · exact ⟨.refl _, SignedStructural.row_refl _⟩

theorem handledArgument_solution :
    (principal OperationalTypingExamples.handledArgument).Holds
      (Model 1 Nat) (SignedStructural.rowView 1 Nat)
      (Inference.extend Empty.elim pureUnit) := by
  apply (RecursiveEffects.principal_exact (Model 1 Nat) (SignedStructural.rowView 1 Nat)
    (signatures 1 Nat) (erase OperationalTypingExamples.handledArgument)
    (signatureTerms Nat Empty) [] [] Empty.elim
    (RecursiveEffects.EnvRel.nil _ _ _ _) (fun _ => rfl) pureUnit).mpr
  exact handledArgument_typing

theorem handledArgument_bound_from_solution :
    Computation.BoundedBy [] (eval Env.nil OperationalTypingExamples.handledArgument) :=
  principal_effect_bound OperationalTypingExamples.handledArgument pureUnit handledArgument_solution

/-- The solved pure row describes the same evaluation already checked directly. -/
theorem handledArgument_result :
    eval Env.nil OperationalTypingExamples.handledArgument = .pure (8 : Nat) :=
  OperationalTypingExamples.handledArgument_eval

end Yulang.OperationalCorrespondenceExamples
