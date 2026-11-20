import Yulang.GeneralSourceMetadataRoleFixture291

/-! Diagnostic refinement of the same ConstructorUse decision. This is
source coverage information, not a new language rejection. -/
namespace Yulang.GeneralSourceMetadataProblem291
open GeneralDeclarationPatterns (Constructors ParameterKind)
open GeneralNominalInspection (Interpretation)
open GeneralSourceMetadataUse291 (Use supported supported_exact)
open GeneralNominalCenteredHeadWFSource (ConstructorUse)

inductive Problem where
  | unknownConstructor
  | wrongArity (actual : Nat)
  | primitiveLayout
  | missingClassification
  | unsupportedNominalLayout
  deriving DecidableEq, Repr

def problem (c : Constructors) (i : Interpretation) (u : Use) : Option Problem :=
  match c u.1 with
  | none => some .unknownConstructor
  | some d =>
    if d.parameters.length ≠ u.2 then some (.wrongArity d.parameters.length)
    else match i.primitives u.1 with
      | some p => if d.parameters = p.parameters then none else some .primitiveLayout
      | none => if !i.invariantNominal u.1 then some .missingClassification
        else if d.parameters = List.replicate u.2 .type then none else some .unsupportedNominalLayout

theorem empty_iff_supported (c : Constructors) (i : Interpretation) (key arity : Nat) :
    problem c i (key,arity) = none ↔ supported c i (key,arity) = true := by
  unfold problem supported
  dsimp only
  cases hc : c key with
  | none => simp
  | some d =>
    by_cases size : d.parameters.length = arity
    · cases hp : i.primitives key with
      | some p =>
        have no : i.invariantNominal key = false := by
          cases h : i.invariantNominal key
          · rfl
          · rw [i.disjoint key h] at hp; cases hp
        simp [size,no]
      | none =>
        cases h : i.invariantNominal key <;> simp [size]
    · simp [size]

theorem empty_iff_use (c : Constructors) (i : Interpretation) (u : Use) :
    problem c i u = none ↔ ConstructorUse c i u.1 u.2 :=
  (empty_iff_supported c i u.1 u.2).trans (supported_exact c i u.1 u.2)

end Yulang.GeneralSourceMetadataProblem291
