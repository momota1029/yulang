import Yulang.GeneralDeclarativeSourceEmission322

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeEmissionOperands322
open GeneralDeclarativeSourceEmission322 (Names useArg inputs)
open GeneralDeclarativeExistingClause322 (Refers)
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeSubstitution320 (logical)
open GeneralDeclarativeEqualities322 (Derives)
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open CommonRoleOutermostResolver (All₂)

def Compound (p : Pattern) : Prop := ∀ n, normalize p ≠ .var n

/-- No equality is needed for a bare where binder: the source emitter
already uses its exact logical lower, center and upper. Compound operands
retain the independent ordinary readback obligation. -/
theorem input_proof {s : State} {names : Names} {fallback : Capture}
    (compiled : translate c interp (normalize pattern) = some code)
    (compound : Compound pattern → Refers s names.input code fallback) :
    Refers s names.input code (useArg names fallback pattern) := by
  match shape : normalize pattern with
  | .var name =>
    have eq : code = .variable name := Option.some.inj (compiled.symm.trans (by rw [shape]; rfl))
    subst code
    rw [GeneralDeclarativeSourceEmission322.source_var names fallback pattern shape]
    exact ⟨.refl _,.refl _,.refl _⟩
  | .app key args =>
    rw [useArg,shape]
    exact compound (by intro n impossible; rw [shape] at impossible; cases impossible)
  | .record label payload tail =>
    rw [useArg,shape]
    exact compound (by intro n impossible; rw [shape] at impossible; cases impossible)
  | .variant tag payload =>
    rw [useArg,shape]
    exact compound (by intro n impossible; rw [shape] at impossible; cases impossible)
  | .join a b =>
    rw [useArg,shape]
    exact compound (by intro n impossible; rw [shape] at impossible; cases impossible)

theorem ordered_inputs {s : State} {names : Names} {ps : List Pattern} {codes : List Expr}
    (order : All₂ (fun p e => translate c interp (normalize p) = some e) ps codes)
    (start : Nat) (compound : Nat → Capture)
    (proofs : ∀ (j : Nat) p code, ps[j]? = some p → codes[j]? = some code →
      Compound p → Refers s names.input code (compound (start+j))) :
    All₂ (Refers s names.input) codes (inputs names compound start ps) := by
  induction order generalizing start with
  | nil => exact .nil
  | @cons pattern code ps codes compiled tail ih =>
    refine .cons (input_proof compiled (proofs 0 pattern code rfl rfl)) ?_
    apply ih
    intro j pat code pFound cFound nonVar
    have exactPos : start + 1 + j = start + (j+1) := by omega
    rw [exactPos]
    exact proofs (j+1) pat code pFound cFound nonVar

end Yulang.GeneralDeclarativeEmissionOperands322
