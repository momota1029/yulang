import Yulang.CommonEffectUniversalPayload

/-! Elimination for the actual universally quantified arm `k payload`.
The continuation returns the full original action computation, including its
unsubtracted row. This does not eliminate arbitrary universal arm bodies. -/
namespace Yulang.CommonEffectUniversalResumption
open Core.PresenceGeneration
open CommonEffectRequestGeneration
open CommonEffectArmGeneration (generateArms generate_arms_exact)
open CommonEffectUniversalPayload (localIdentity)

/-- An independent typing inversion, uniformly over all Common types/rows and
all captured bindings. No generated formula or solver is used in this rule. -/
theorem resume_payload_iff (bindings : List (Binding Common.model)) (payload : Common.Ty)
    (input out : Computation) :
    Typing Common.model
      (.mono (Comp.pure Common.model payload) ::
       .mono (Comp.pure Common.model (Comp.arrow Common.model (Comp.pure Common.model payload) input)) :: bindings)
      (.app (.var 1) (.var 0)) out ↔ Comp.le Common.model input out := by
  constructor
  · intro typed
    obtain ⟨argument, result, effects, functionTyped, _, bound⟩ := (Typing.app_iff _ _ _ _ _).mp typed
    have functionBound : Comp.le Common.model
        (Comp.pure Common.model (Comp.arrow Common.model (Comp.pure Common.model payload) input))
        (Comp.arrow Common.model argument result, effects) := by
      simpa [Typing.var_iff, BindingLookup, BindingTyping.mono_iff] using functionTyped
    have parts := (Common.common_arrow_iff payload argument.1 input.1 result.1
      Common.rowEmpty argument.2 input.2 result.2).mp functionBound.1
    refine ⟨Common.subtype_trans parts.2.2.1 bound.1, ?_⟩
    intro occurrence present
    exact bound.2 occurrence (Or.inr (parts.2.2.2 occurrence present))
  · intro bound
    apply Typing.app (a := Comp.pure Common.model payload) (b := input) (ef := Common.rowEmpty)
    · exact .var rfl (.mono ⟨Common.subtype_refl _, Common.rowLe_refl _⟩)
    · exact .var rfl (.mono ⟨Common.subtype_refl _, Common.rowLe_refl _⟩)
    · refine ⟨bound.1, ?_⟩
      intro occurrence present
      exact present.elim False.elim (bound.2 occurrence)

/-- The semantic statement of actual generated forall/exists elimination. -/
theorem generate_resumption_arm_exact (environment : SchemeEnv α) (bindings : List (Binding Common.model))
    (assignment : α → Computation) (related : EnvRel Common.model assignment environment bindings)
    (key : Nat) (input out : CompTerm α) :
    (generateArms (scopes := scopes) environment (fun _ : Fin 1 => localIdentity key)
      input out (fun _ => .app (.var 1) (.var 0))).Holds assignment ↔
      Comp.le Common.model (input.eval Common.model assignment) (out.eval Common.model assignment) := by
  rw [generate_arms_exact environment bindings assignment related]
  simp only [localIdentity]
  constructor
  · intro universal
    obtain ⟨operated, valid⟩ := universal (fun _ _ => .top)
    have resumeBound := (resume_payload_iff bindings .top (input.eval Common.model assignment) (operated 0)).mp
      (by simpa [TyTerm.eval, localEnv, Comp.pure] using (valid 0).1)
    exact ⟨Common.subtype_trans resumeBound.1 (valid 0).2.1,
      Common.rowLe_trans resumeBound.2 (valid 0).2.2⟩
  · intro bound locals
    refine ⟨fun _ => input.eval Common.model assignment, fun i => ⟨?_, bound⟩⟩
    apply (resume_payload_iff bindings (locals i 0) (input.eval Common.model assignment) _).mpr
    exact ⟨Common.subtype_refl _, Common.rowLe_refl _⟩

/-- The real generated universal body is replaced by a finite comparison.
All parameters remain unrestricted, and no universal check survives in it. -/
theorem eliminate_resumption_arm (environment : SchemeEnv α) (bindings : List (Binding Common.model))
    (assignment : α → Computation) (related : EnvRel Common.model assignment environment bindings)
    (key : Nat) (input out : CompTerm α) :
    (generateArms (scopes := scopes) environment (fun _ : Fin 1 => localIdentity key)
      input out (fun _ => .app (.var 1) (.var 0))).Holds assignment ↔
      (CommonEffectFormula.Formula.compLe (scopes := scopes) input out).Holds assignment :=
  generate_resumption_arm_exact environment bindings assignment related key input out
end Yulang.CommonEffectUniversalResumption
