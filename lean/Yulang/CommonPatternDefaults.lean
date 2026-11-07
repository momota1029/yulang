import Yulang.CommonPatternEnvironment
import Yulang.CommonOptionalBound

/-!
# Finite Common constraints for the optional input of a pattern default

Pattern defaults test the original record's optional payload. A strict record
extension is a different operation: it evaluates its fallback even when the
field is present. We use the independent `OptionalPayload` observation here,
and compile it to a finite disjunction of ordinary Common subtype constraints.
The unconstrained top-payload branch is necessary at constructor depth zero.
-/

namespace Yulang.CommonPatternDefaults

open Core.PresenceGeneration
open CommonDefaultRequired (OptionalPayload)

/-- No semantic predicate or source typing is embedded as a formula atom. -/
def optionalConstraints (label : Nat) (source payload : TyTerm α) : Formula α :=
  .or (.and (.tyLe .top payload) (.tyLe source .emptyRecord))
    (.tyLe source (.union .exactEmpty (.required label payload)))

/-- All shared slot assignments and all Common payloads are admitted, including
regular types and top. The result preserves the full optional observation,
without replacing the original record by its selected field. -/
theorem optional_constraints_exact (ρ : α → Comp Common.model)
    (label : Nat) (source payload : TyTerm α) :
    (optionalConstraints label source payload).Holds Common.model ρ ↔
      OptionalPayload label (source.eval Common.model ρ) (payload.eval Common.model ρ) := by
  simpa only [optionalConstraints, Formula.Holds, TyTerm.eval,
    Common.model, CommonOptionalBound.guardedOptional] using
    (CommonOptionalBound.optional_payload_branches_exact label
      (source.eval Common.model ρ) (payload.eval Common.model ρ)).symm

/-- The payload-selection premise of a default pattern. This is independent of
constraint formulas. It does not decide whether a required/default source
annotation is legal, run the matcher, or type the remaining pattern. The row
is the statically possible fallback row, before the surrounding pattern joins
it with the other checks. -/
inductive DefaultInputTyping
    (environment : List (Binding Common.model)) (label : Nat)
    (source : Common.Ty) (fallback : Inference.Expr) : Comp Common.model → Prop where
  | select : OptionalPayload label source payload →
      Typing Common.model environment fallback fallbackResult →
      Comp.le Common.model (.union payload fallbackResult.1, fallbackResult.2) result →
      DefaultInputTyping environment label source fallback result

/-- A finite generator for that premise, with two bound slots and no new atom.
The first slot's value is the optional payload and its row is unused; the second
is the fallback computation. Existing slots remain shared, free parameters. -/
def generateDefaultInput (environment : SchemeEnv α) (label : Nat)
    (source : TyTerm α) (fallback : Inference.Expr) (result : CompTerm α) : Formula α :=
  .existsSlot (.existsSlot (
    .and (optionalConstraints label (source.rename fun x => some (some x)) fresh₀.ty)
      (.and (generate (env₂ environment) fallback fresh₁)
        (Formula.compLe ⟨.union fresh₀.ty fresh₁.ty, fresh₁.row⟩ (lift₂ result)))))

/-- Exact finite generation of the default-input premise for every source type,
free assignment, requested value/row result and related captured environment.
No success, closedness, satisfiability, or restrictions on parameters are assumed. -/
theorem default_input_generation_exact
    (ρ : α → Comp Common.model) (symbolic : SchemeEnv α)
    (semantic : List (Binding Common.model))
    (outer : EnvRel Common.model ρ symbolic semantic)
    (label : Nat) (source : TyTerm α) (fallback : Inference.Expr) (result : CompTerm α) :
    (generateDefaultInput symbolic label source fallback result).Holds Common.model ρ ↔
      DefaultInputTyping semantic label (source.eval Common.model ρ) fallback
        (result.eval Common.model ρ) := by
  have hf (a b : Comp Common.model) :
      (generate (env₂ symbolic) fallback fresh₁).Holds Common.model
        (extend (extend ρ a) b) ↔ Typing Common.model semantic fallback b := by
    simpa only [env₂, fresh₁, CompTerm.eval_var, extend_none] using
      generate_models_iff_typing Common.model fallback _ _ _ fresh₁
        ((outer.lift a).lift b)
  have hp (a b : Comp Common.model) :
      (optionalConstraints label (source.rename fun x => some (some x)) fresh₀.ty).Holds
          Common.model (extend (extend ρ a) b) ↔
        OptionalPayload label (source.eval Common.model ρ) a.1 := by
    simpa [fresh₀, CompTerm.var, TyTerm.eval, Function.comp_def] using
      optional_constraints_exact (extend (extend ρ a) b) label
        (source.rename fun x => some (some x)) fresh₀.ty
  have hc (a b : Comp Common.model) :
      (Formula.compLe ⟨.union fresh₀.ty fresh₁.ty, fresh₁.row⟩ (lift₂ result)).Holds
          Common.model (extend (extend ρ a) b) ↔
        Comp.le Common.model (.union a.1 b.1, b.2) (result.eval Common.model ρ) := by
    simp [Formula.compLe, Formula.Holds, Comp.le, CompTerm.eval, CompTerm.var,
      CompTerm.rename, fresh₀, fresh₁, lift₂, TyTerm.eval, RowTerm.eval,
      Function.comp_def, Common.model, extend]
  simp only [generateDefaultInput, Formula.Holds, hp, hf, hc]
  constructor
  · rintro ⟨a, b, optional, fallbackTyped, selected⟩
    exact .select optional fallbackTyped selected
  · intro typed
    cases typed with
    | select optional fallbackTyped selected =>
        exact ⟨(_, Common.rowEmpty), _, optional, fallbackTyped, selected⟩

end Yulang.CommonPatternDefaults
