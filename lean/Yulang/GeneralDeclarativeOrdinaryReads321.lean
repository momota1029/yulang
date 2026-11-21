import Yulang.GeneralDeclarativeAliasMeaning321
import Yulang.GeneralDeclarativeCompileLists321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeOrdinaryReads321
open GeneralDeclarativeHead320 (State Models Equation)
open GeneralDeclarativeAliasMeaning321 (alias_sound)
open GeneralDeclarativeLowerKnown321 (Alias)
open GeneralDeclarativeEntailment320 (Entails Holds)
open GeneralDeclarativeSubstitution320 (EquationRead equation_read logical logical_value)
open GeneralDeclarativeWhere319 (Capture variables)
open GeneralNominalMaterialization (Mode)
open GeneralNominalCenteredHeadMatExpressions (Expr value)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans)
open CommonNominalFullCarrier (Equivalent)

/-- Reads can traverse ordinary logical equality as well as syntactic
constructor equations. They neither inspect a solver nor contain Models. -/
inductive Reads (s : State) (capture : Nat → Capture) (mode : Mode) : Nat → Expr → Prop where
  | fact : EquationRead s capture mode name exp → Reads s capture mode name exp
  | alias : Alias s name other → Reads s capture mode other exp → Reads s capture mode name exp

theorem read_sound {s : State} (proof : Reads s capture mode name exp) (m) (valid : Models s m) :
    Equivalent (m name).1 (value (variables capture m) mode exp) := by
  induction proof with
  | fact h => exact equation_read h m valid
  | alias link _ ih => exact eqv_trans (alias_sound link m valid) ih

theorem entails_read {s : State} (proof : Reads s capture mode name exp) :
    Entails s ⟨name,logical capture mode exp⟩ := by
  intro m valid
  simp only [Holds,logical_value]
  exact read_sound proof m valid

end Yulang.GeneralDeclarativeOrdinaryReads321
