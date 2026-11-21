import Yulang.GeneralDeclarativeCovariantProbe326
import Yulang.GeneralDeclarativeProjectedFrame326

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeCovariantFrame326
open GeneralDeclarativePairDecl326
open GeneralDeclarativeCovariantState326
open GeneralDeclarativeCovariantProbe326
open GeneralDeclarativeProjectedFrame326 (Frame)
open GeneralDeclarativeFrameReadback325 (sourceNames)
open GeneralDeclarativeEmissionForest322 (Placement children)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeExampleSource320 (leaf point)

abbrev parentBase (n : Nat) : Capture := if n = 0 then leftArg else rightArg
abbrev leafBase (_ : Nat) : Capture := leftArg
abbrev placement : Placement := ⟨fun _ _ => point 900,fun _ _ => 5⟩

theorem child_exact : children impl (sourceNames impl placement parentBase) placement = [child] := rfl

theorem parent_frame (done : Nat → Prop) : Frame final reg interpret (support2 done) root impl parentBase placement := by
  refine ⟨.cons ⟨root_range,.projected normalized center .capture .capture ?_⟩ .nil,?_ ,?_ ,
    [parentRow],rfl,fun _ h => List.mem_append_left _ (List.mem_append_right _ h)⟩
  · intro o found
    rcases List.mem_cons.mp found with rfl|next
    · exact .refl _
    · cases List.mem_singleton.mp next
      exact .refl _
  · intro n mentioned
    change n ∈ [0,1] at mentioned
    rcases List.mem_cons.mp mentioned with rfl|later
    · exact left_range
    · cases List.mem_singleton.mp later
      exact right_range
  · intro cl seen
    cases List.mem_singleton.mp seen
    constructor
    · refine ⟨[.variable 0],rfl,?_⟩
      intro n p e index _ no
      cases List.mem_singleton.mp (List.mem_of_getElem? index)
      exact False.elim (no 0 rfl)
    · intro eq named
      cases List.mem_singleton.mp named
      exact ⟨.variable 2,rfl,fun need => False.elim (need ⟨2,rfl,List.mem_cons_self⟩)⟩

theorem child_frame (done : Nat → Prop) : Frame final reg interpret (support2 done) child leaf leafBase placement := by
  refine ⟨.cons ⟨left_range,.ordinary (.actual rfl .capture ?_)⟩ .nil,fun _ _ => left_range,
    fun _ never => False.elim (List.not_mem_nil never),[childRow],rfl,fun _ h => List.mem_append_right _ h⟩
  intro o found
  cases List.mem_singleton.mp found
  exact .refl _

end Yulang.GeneralDeclarativeCovariantFrame326
