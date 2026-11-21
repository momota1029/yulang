import Yulang.GeneralNominalCenteredHeadMatExpressions
import Yulang.GeneralFiniteTypedWrites312
import Yulang.CommonNominalFullConstructors

set_option backward.isDefEq.respectTransparency false
/-! A pattern normalizing to a variable may still compile to joins. Its
compiled value equals that binder in every evaluation mode, not just actual. -/
namespace Yulang.GeneralVersionedNormalizedVariable313
open GeneralDeclarationPatterns GeneralNominalCenteredHeadMatExpressions
open CommonNominalFullCarrier

theorem row_not_var (entries : List (Nat × Pattern)) : rowPattern entries ≠ .var name := by
  cases entries with
  | nil => intro h; cases h
  | cons top rest =>
    cases rest <;> intro eq <;> cases top <;> cases eq

theorem merge_variable {a b : Pattern} (found : merge a b = .var name) :
    a = .var name ∧ b = .var name := by
  unfold merge at found
  split at found
  · rename_i same
    exact ⟨found,same.symm.trans found⟩
  · split at found
    · exact False.elim (row_not_var _ found)
    · cases found

theorem normalized_value (pattern : Pattern) (found : normalize pattern = .var name)
    (compiled : translate catalogue interp pattern = some expr)
    (variables : GeneralNominalMaterialization.Mode → Nat → Ty) (mode) :
    Equivalent (value variables mode expr) (variables mode name) := by
  cases pattern with
  | var v =>
    cases Pattern.var.inj found
    cases Option.some.inj compiled
    exact GeneralFiniteTypedWrites312.reflexive _
  | app | record | variant =>
    rw [normalize] at found
    cases found
  | join first last =>
    rw [normalize] at found
    obtain ⟨leftName,rightName⟩ := merge_variable found
    cases left : translate catalogue interp first with
    | none => simp [translate,left] at compiled
    | some x =>
      cases right : translate catalogue interp last with
      | none => simp [translate,left,right] at compiled
      | some y =>
        simp only [translate,left,right,bind,pure,Option.bind,Option.some.injEq] at compiled
        subst expr
        have one := normalized_value first leftName left variables mode
        have two := normalized_value last rightName right variables mode
        change Equivalent (.union (value variables mode x) (value variables mode y)) _
        exact ⟨(common_union_is_join ..).mpr ⟨one.1,two.1⟩,
          subtype_trans one.2 ((common_union_is_join ..).mp (subtype_refl _)).1⟩
 termination_by sizeOf pattern

end Yulang.GeneralVersionedNormalizedVariable313
