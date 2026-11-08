import Yulang.CommonEffectMixedExact
import Yulang.CommonEffectMixedKinds

/-!
Checked finite generation at the resolved source boundary. Declaration
admission is computed from the original captured-name table and both local
sorts, rather than assumed by a caller. The semantic operation table is
computed from those same declarations and the same captured assignment.
This is constraint-generation exactness, not a solver for universal formulas.
-/
namespace Yulang.CommonEffectMixedChecked
open Core.PresenceGeneration (CompTerm)
open CommonEffectRequestGeneration (Computation)
open CommonEffectKindedFormula
open CommonEffectMixedDeclarations (Declarations interpretAll)
open CommonEffectMixedKinds (Kind DeclarationsKinded checkDeclarations check_declarations_exact)
open CommonEffectMixedSource (Expr Binding Typing)
open CommonEffectMixedGeneration (EnvRel)

variable {scopes : Nat}

def generateChecked (captured : List Kind) (declarations : Declarations Nat)
    (schemes : SchemeEnv scopes Nat) (body : Expr scopes) (out : CompTerm Nat) : Formula scopes Nat :=
  if checkDeclarations captured declarations then
    CommonEffectMixedGeneration.generate declarations schemes body out
  else .core .bot

/-- Full recursive generation iff for a finite mixed table. The sole context
hypothesis relates the given input bindings to the given input schemes; kind
admission is part of the returned constraint, not a premise. -/
theorem generate_checked_exact (captured : List Kind) (declarations : Declarations Nat)
    (schemes : SchemeEnv scopes Nat) (bindings : List (Binding scopes))
    (assignment : Nat → Computation)
    (related : EnvRel (interpretAll assignment declarations) assignment schemes bindings)
    (body : Expr scopes) (out : CompTerm Nat) :
    (generateChecked captured declarations schemes body out).Holds assignment ↔
      DeclarationsKinded captured declarations ∧
      Typing (interpretAll assignment declarations) bindings body (out.eval Common.model assignment) := by
  have raw := CommonEffectMixedExact.generate_recursive_mixed_exact
    (interpretAll assignment declarations) body schemes bindings assignment out ⟨rfl, related⟩
  cases checked : checkDeclarations captured declarations with
  | false =>
    have invalid : ¬ DeclarationsKinded captured declarations := by
      intro valid
      have impossible := (check_declarations_exact captured declarations).mpr valid
      simp [checked] at impossible
    simp [generateChecked, checked, invalid, Core.PresenceGeneration.Formula.Holds]
  | true =>
    have valid := (check_declarations_exact captured declarations).mp checked
    simpa only [generateChecked, checked, ↓reduceIte, valid, true_and] using raw

/-- No environment relation is supplied for a closed expression. All finite
mixed declarations, original expressions, captured assignments and result
descriptions are quantified, including failed kind checks and bad lookups. -/
theorem generate_closed_checked_exact (captured : List Kind) (declarations : Declarations Nat)
    (assignment : Nat → Computation) (body : Expr scopes) (out : CompTerm Nat) :
    (generateChecked captured declarations [] body out).Holds assignment ↔
      DeclarationsKinded captured declarations ∧
      Typing (interpretAll assignment declarations) [] body (out.eval Common.model assignment) :=
  generate_checked_exact captured declarations [] [] assignment
    (EnvRel.nil _ _) body out

end Yulang.CommonEffectMixedChecked
