import Yulang.GeneralDeclarativeK2Graph321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeK2Alias321
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeLowerKnown321 (Alias alias_refl alias_symm)
open GeneralDeclarativeK2Graph321 (View Descends Path OnCycle aliasView edge_transport)

def AliasCycle (s : State) (observed : View) (root : Nat) : Prop :=
  ∃ descended last, Descends (aliasView s observed) root descended ∧
    Path (aliasView s observed) descended last ∧ Alias s last root

theorem cycle_alias {s observed root other}
    (link : Alias s root other) (cycle : AliasCycle s observed other) :
    AliasCycle s observed root := by
  obtain ⟨next,last,first,back,same⟩ := cycle
  exact ⟨next,last,edge_transport link first,back,.trans same (alias_symm link)⟩

theorem alias_cycle_iff {s observed root other} (link : Alias s root other) :
    AliasCycle s observed root ↔ AliasCycle s observed other :=
  ⟨cycle_alias (alias_symm link),cycle_alias link⟩

theorem cycle_in_alias_graph {s observed root} (cycle : OnCycle (aliasView s observed) root) :
    AliasCycle s observed root := by
  obtain ⟨next,first,remaining⟩ := cycle
  exact ⟨next,root,first,remaining,alias_refl root⟩

theorem no_nonempty_alias_only {s observed root}
    (none : ∀ a, Alias s root a → ∀ h, ¬observed a h) :
    ¬AliasCycle s observed root := by
  rintro ⟨next,last,⟨shape,⟨source,alias,seen⟩,_⟩,_⟩
  exact none source alias shape seen

end Yulang.GeneralDeclarativeK2Alias321
