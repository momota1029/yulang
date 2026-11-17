import Yulang.GeneralPresenceOrderedBlock247

/-! An ordered block is independent of initial private type values. This gives
literal absorption of later writes within its target set, without requiring
those later writes to form an ordered block. Actual source ordering remains a
separate producer obligation; no analogous law for arbitrary cycles is claimed. -/
namespace Yulang.GeneralPresenceOrderedDependence247
open Core.PresenceGeneration
open GeneralPresenceDefinitionRewrite244 GeneralPresenceOrderedBlock247
variable {Name : Type} [DecidableEq Name]

theorem solve_equal (model : Model) (entries : List (Entry Name)) (safe : SafeOrder entries)
    (first last : Name → Comp model)
    (rows : ∀ name, (first name).2 = (last name).2)
    (outside : ∀ name, (∀ entry ∈ entries, entry.1 ≠ name) → (first name).1 = (last name).1) :
    solve model entries first = solve model entries last := by
  induction entries generalizing first last with
  | nil =>
    funext name
    exact Prod.ext (outside name (by simp)) (rows name)
  | cons entry rest ih =>
    obtain ⟨noSelf,distinct,unread,tailSafe⟩ := safe
    have rhsEqual : entry.2.eval model first = entry.2.eval model last := by
      apply GeneralPresenceConsumerSupport246.type_eval_equal model first last rows entry.2
      intro name member
      apply outside name
      intro later present equal
      rcases List.mem_cons.mp present with rfl | present
      · exact noSelf (equal ▸ member)
      · exact unread later present (equal ▸ member)
    change solve model rest (put model first entry.1 (entry.2.eval model first)) =
      solve model rest (put model last entry.1 (entry.2.eval model last))
    apply ih tailSafe
    · intro name
      exact (put_rows model first entry.1 _ name).trans
        ((rows name).trans (put_rows model last entry.1 _ name).symm)
    · intro name tailOutside
      by_cases same : name = entry.1
      · subst name
        simpa only [put,ite_true] using rhsEqual
      · rw [put_outside model first entry.1 _ name (Ne.symm same),
          put_outside model last entry.1 _ name (Ne.symm same)]
        apply outside name
        intro later member
        rcases List.mem_cons.mp member with rfl | member
        · exact Ne.symm same
        · exact tailOutside later member

def TargetsWithin (fresh old : List (Entry Name)) : Prop :=
  ∀ entry ∈ fresh, ∃ original ∈ old, original.1 = entry.1

theorem solve_absorbs (model : Model) (old fresh : List (Entry Name))
    (safe : SafeOrder old) (within : TargetsWithin fresh old)
    (assignment : Name → Comp model) :
    solve model old (solve model fresh assignment) = solve model old assignment := by
  apply solve_equal model old safe _ assignment (solve_rows model fresh assignment)
  intro name outside
  apply congrArg Prod.fst (solve_outside model fresh assignment name ?_)
  intro entry member
  obtain ⟨original,present,equal⟩ := within entry member
  rw [← equal]
  exact outside original present

theorem solve_idempotent (model : Model) (entries : List (Entry Name))
    (safe : SafeOrder entries) (assignment : Name → Comp model) :
    solve model entries (solve model entries assignment) = solve model entries assignment :=
  solve_absorbs model entries entries safe (fun entry member => ⟨entry,member,rfl⟩) assignment

end Yulang.GeneralPresenceOrderedDependence247
