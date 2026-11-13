import Yulang.GeneralPatternConservativeSubstitution

/-! A normalized covered template need not commute with raw substitution.
An erased record field exposes the distinction between row grouping and
recursive payload normalization. The production boundary uses normal forms. -/
namespace Yulang.GeneralPatternHiddenJoin
open GeneralDeclarationPatterns

def first : Pattern := .join (.variant 7 (.var 0)) (.variant 7 (.var 1))
def last : Pattern := .variant 7 (.join (.var 0) (.var 1))
def template : Pattern := .record 3 (.app 0 [])
  (.join (.record 3 first (.app 0 [])) (.record 3 last (.app 0 [])))
def capture (name : Nat) : Pattern :=
  .variant 8 (.app (if name = 0 then 0 else 1) [])

theorem same_before : normalize first = normalize last := by decide +kernel
theorem covered_normal : covered (normalize template) = true := by decide +kernel
theorem erased_before : normalize template = .record 3 (.app 0 []) (.app 0 []) := by decide +kernel
theorem different_after : normalize (first.subst capture) ≠ normalize (last.subst capture) := by decide +kernel
theorem raw_substitution_does_not_commute :
    normalize (template.subst capture) ≠ normalize ((normalize template).subst capture) := by decide +kernel
theorem normalized_mass : GeneralNominalPatersonLineage.mass
    (substArgs capture (normalizeArgs [template,.var 0,.var 1])) = 7 := by decide +kernel
theorem raw_mass : GeneralNominalPatersonLineage.mass
    (substArgs capture [template,.var 0,.var 1]) = 22 := by decide +kernel

end Yulang.GeneralPatternHiddenJoin
