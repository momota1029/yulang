import Yulang.GeneralDeclarativeRecordProbe326
import Yulang.GeneralDeclarativeProjectedFrame326

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeRecordFrame326
open GeneralDeclarativeRecordDecl326
open GeneralDeclarativeRecordState326
open GeneralDeclarativeRecordProbe326 (trace)
open GeneralDeclarativeHiddenDecl324 (catalogue interpretation)
open GeneralDeclarativeProjectedFrame326 (Frame)
open GeneralDeclarativeFrameReadback325 (sourceNames)
open GeneralDeclarativeEmissionForest322 (Placement children)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeExampleSource320 (point leaf)
open GeneralDeclarativePairDecl326 (clause)

abbrev base (n : Nat) : Capture := point (if n = 0 then 3 else 7)
abbrev childBase (_ : Nat) : Capture := point 3
abbrev place : Placement := ⟨fun _ _ => point 990,fun _ _ => 5⟩

theorem generated_child : children decl (sourceNames decl place base) place = [child] := rfl
theorem tail_name : (sourceNames decl place base).input 1 = point 7 := rfl

theorem root_frame (done : Nat → Prop) : Frame final registry interpretation (support2 done) root decl base place := by
  refine ⟨.cons ⟨point_bound 0,.ordinary (.actual normal (trace done .actual) ?_)⟩ .nil,
    fun _ _ => point_bound _,?_,[parentRow],rfl,fun _ h => List.mem_append_left _ (List.mem_append_right _ h)⟩
  · intro item whereIs
    rcases List.mem_cons.mp whereIs with rfl|next
    · exact .refl _
    · cases List.mem_singleton.mp next
      exact .refl _
  · intro cl inside
    cases List.mem_singleton.mp inside
    constructor
    · refine ⟨[.variable 0],rfl,?_⟩
      intro n p code pos _ impossible
      cases List.mem_singleton.mp (List.mem_of_getElem? pos)
      exact False.elim (impossible 0 rfl)
    · intro eq used
      cases List.mem_singleton.mp used
      exact ⟨.variable 2,rfl,fun need => False.elim (need ⟨2,rfl,List.mem_cons_self⟩)⟩

theorem child_frame (done : Nat → Prop) : Frame final registry interpretation (support2 done) child leaf childBase place := by
  refine ⟨.cons ⟨point_bound 3,.ordinary (.actual rfl .capture ?_)⟩ .nil,fun _ _ => point_bound 3,
    fun _ impossible => False.elim (List.not_mem_nil impossible),[childRow],rfl,fun _ used => List.mem_append_right _ used⟩
  intro o used
  cases List.mem_singleton.mp used
  exact .refl _

end Yulang.GeneralDeclarativeRecordFrame326
