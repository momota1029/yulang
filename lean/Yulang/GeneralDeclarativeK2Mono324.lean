import Yulang.GeneralDeclarativeK2Alias321
import Yulang.GeneralDeclarativeGraphRows321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeK2Mono324
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeK2Graph321 (Path Descends View aliasView)
open GeneralDeclarativeLowerKnown321 (alias_mono)
open GeneralDeclarativeGraphRows321 (observed)

theorem port_edge {s t : State} {a b : View}
    (normal : s.normal = t.normal) (ordinary : s.equations ⊆ t.equations)
    (port : ∀ n shape, a n shape → b n shape)
    (old : Descends (aliasView s a) x y) : Descends (aliasView t b) x y := by
  obtain ⟨head,⟨origin,alias,known⟩,there⟩ := old
  exact ⟨head,⟨origin,alias_mono normal ordinary alias,port origin head known⟩,there⟩

theorem port_path {s t : State} {a b : View}
    (normal : s.normal = t.normal) (ordinary : s.equations ⊆ t.equations)
    (port : ∀ n shape, a n shape → b n shape)
    (old : Path (aliasView s a) x y) : Path (aliasView t b) x y := by
  induction old with
  | refl => exact .refl _
  | next head _ ih => exact .next (port_edge normal ordinary port head) ih

/-- Ordinary equations are visible to K2 even while their origin is
unsupported for expansion. Adding equations cannot erase a witnessed
cycle in this normalized-row fragment; it may create one. -/
theorem preserve {s t : State} (normal : s.normal = t.normal)
    (ordinary : s.equations ⊆ t.equations)
    (old : AliasCycle s (observed s) root) : AliasCycle t (observed t) root := by
  have port : ∀ n head, observed s n head → observed t n head := by
    intro n head desc
    obtain ⟨exp,found,shaped⟩ := desc
    exact ⟨exp,ordinary found,shaped⟩
  obtain ⟨first,last,edge,path,back⟩ := old
  exact ⟨first,last,port_edge normal ordinary port edge,port_path normal ordinary port path,
    alias_mono normal ordinary back⟩

end Yulang.GeneralDeclarativeK2Mono324
