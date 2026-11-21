import Yulang.GeneralDeclarativeK2Alias321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeRank321
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeLowerKnown321 (Alias)
open GeneralDeclarativeK2Graph321 (View Descends Path aliasView)
open GeneralDeclarativeK2Alias321 (AliasCycle)

theorem path_nonincreasing {view : View} {weight : Nat → Nat}
    (decreases : ∀ a b, Descends view a b → weight b < weight a)
    (path : Path view a b) : weight b ≤ weight a := by
  induction path with
  | refl => exact Nat.le_refl _
  | next edge _ ih => exact Nat.le_trans ih (Nat.le_of_lt (decreases _ _ edge))

theorem graph_no_cycle {s : State} {view : View} (weight : Nat → Nat)
    (aliases : ∀ a b, Alias s a b → weight a = weight b)
    (children : ∀ a tag b, view a tag → b ∈ tag.children → weight b < weight a) :
    ∀ root, ¬AliasCycle s view root := by
  intro root cycle
  have decreases : ∀ a b, Descends (aliasView s view) a b → weight b < weight a := by
    rintro a b ⟨tag,⟨source,same,existsHead⟩,there⟩
    rw [aliases a source same]
    exact children source tag b existsHead there
  obtain ⟨child,last,first,back,same⟩ := cycle
  have impossible := Nat.lt_of_le_of_lt (path_nonincreasing decreases back) (decreases root child first)
  rw [aliases last root same] at impossible
  exact Nat.lt_irrefl _ impossible

end Yulang.GeneralDeclarativeRank321
