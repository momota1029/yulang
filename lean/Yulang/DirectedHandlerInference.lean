import Yulang.RowInference
import Yulang.DirectedBounds

/-!
# Generated handler constraints compose signed operational bounds

This bridge specializes the shared row-inference rule to signed occurrences and
uses the signed computation kernel's shallow-handler theorem. Satisfying the
generated constraints supplies the row inclusion; semantic bounds for the action
and each arm remain explicit premises. The continuation keeps the original input
row, and neither return-arm nor operation-arm effects are subtracted.

No source evaluator, elaboration theorem, value-typing interpretation, or
origin-invariant preservation is claimed. In particular, this conditional result
does not derive its semantic premises from core typing alone.
-/

namespace Yulang.RowInference

open Inference Directed
open EffectInference (Signature SigKey semanticArmEnvironment)

/-- A checked signed handler rule composes supplied bounds for its runtime parts. -/
theorem generated_signed_handler_composes_effect_bounds [DecidableEq (SigKey F O A)]
    (view : RowView m (signedAlgebra n (SigKey F O A)))
    (sΓ : SchemeEnv α) (Γ : List (Binding m))
    (ρ : α → Comp m) (henv : EnvRel m ρ sΓ Γ) (sig : Signature α F O A)
    (action onReturn onOperation : Expr) (out : CompTerm α)
    (checked : (handlerConstraints sΓ sig action onReturn onOperation out).Holds view ρ)
    (computation : Computation n (SigKey F O A) Payload Response Value)
    (returnRuntime : Value → Computation n (SigKey F O A) Payload Response Result)
    (operationRuntime : Occurrence n (SigKey F O A) → Payload →
      (Response → Computation n (SigKey F O A) Payload Response Value) →
        Computation n (SigKey F O A) Payload Response Result)
    (actionBound : ∀ input, Typing m Γ action input →
      Computation.BoundedBy (view.decode input.2) computation)
    (returnBound : ∀ (input returned : Comp m),
      Typing m (.mono (Comp.pure m input.1) :: Γ) onReturn returned →
      ∀ value, Computation.BoundedBy (view.decode returned.2) (returnRuntime value))
    (operationBound : ∀ (input operated : Comp m),
      Typing m (semanticArmEnvironment m Γ input (sig.input.eval m ρ) (sig.output.eval m ρ))
        onOperation operated →
      ∀ occurrence payload resume, Capturable [sig.key] occurrence →
        (∀ response, Computation.BoundedBy (view.decode input.2) (resume response)) →
        Computation.BoundedBy (view.decode operated.2) (operationRuntime occurrence payload resume)) :
    Computation.BoundedBy (view.decode (out.eval m ρ).2)
      (Computation.shallowHandle [sig.key] returnRuntime operationRuntime computation) := by
  have typed := (handler_constraints_exact (signedAlgebra n (SigKey F O A)) view
    sΓ Γ ρ henv sig action onReturn onOperation out).mp checked
  rcases (handlerTyping_iff (signedAlgebra n (SigKey F O A)) view Γ sig.key
    (sig.input.eval m ρ) (sig.output.eval m ρ) action onReturn onOperation
    (out.eval m ρ)).mp typed with ⟨input, returned, operated, hi, hr, ho, _, inclusion⟩
  apply Computation.bounded_mono inclusion
  apply Computation.shallowHandle_bounded [sig.key] (view.decode input.2)
    (List.append (α := Occurrence n (SigKey F O A)) (view.decode returned.2) (view.decode operated.2))
    returnRuntime operationRuntime
  · intro value
    exact Computation.bounded_mono (fun _ member => List.mem_append.mpr (Or.inl member))
      (returnBound input returned hr value)
  · intro occurrence payload resume captured resumeBound
    exact Computation.bounded_mono (fun _ member => List.mem_append.mpr (Or.inr member))
      (operationBound input operated ho occurrence payload resume captured resumeBound)
  · exact actionBound input hi

end Yulang.RowInference
