import Yulang.GeneralDeclarativeRepeatFrame327
import Yulang.GeneralDeclarativeFrontier327

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 15000
set_option maxHeartbeats 7600000
namespace Yulang.GeneralDeclarativeRepeatResolve327
open GeneralDeclarativeRepeatDecl327
open GeneralDeclarativeRepeatState327
open GeneralDeclarativeRepeatProbe327
open GeneralDeclarativeRepeatGraph327
open GeneralDeclarativeRepeatFrame327
open GeneralDeclarativeProjectedFrame326 (Rule Generated sound)
open GeneralDeclarativeExampleSource320 (leaf)
open GeneralDeclarativeEvidence320 (Evidence)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralDeclarativeHead320 (Models)
open GeneralDeclarativeFrontier327 (CanGenerate NoOverlap coverage)
open CommonRoleOutermostResolver (Classify Dictionary)

abbrev dict : Dictionary := .node impl.id [.node leaf.id []]
abbrev branch (done : Nat → Prop) := Rule result reg interp (supported done) (tests done)

theorem root_only (d) (registered : d ∈ reg.declarations) (role : d.role = root.role) : d = impl := by
  rcases List.mem_cons.mp registered with rfl|tail
  · rfl
  · cases List.mem_singleton.mp tail
    cases role

theorem child_only (d) (registered : d ∈ reg.declarations) (role : d.role = child.role) : d = leaf := by
  rcases List.mem_cons.mp registered with rfl|tail
  · cases role
  · exact List.mem_singleton.mp tail

theorem root_selected (done : Nat → Prop) : branch done root (.selected impl.id [child]) := by
  refine .selected (root_support done) (safe done _) ?_
    ⟨⟨List.mem_cons_self,rfl⟩,root_matches done⟩ ?_
    ⟨base,place,parent_frame done,emitted⟩
  · rintro ⟨d,⟨visible,role⟩,wait⟩
    cases root_only d visible role
    exact wait (root_matches done)
  · rintro d ⟨⟨visible,role⟩,_⟩
    rw [root_only d visible role]

theorem child_selected (done : Nat → Prop) : branch done child (.selected leaf.id []) := by
  refine .selected (child_support done) (safe done _) ?_
    ⟨⟨List.mem_cons_of_mem _ List.mem_cons_self,rfl⟩,child_matches done⟩ ?_
    ⟨childBase,place,child_frame done,rfl⟩
  · rintro ⟨d,⟨visible,role⟩,wait⟩
    cases child_only d visible role
    exact wait (child_matches done)
  · rintro d ⟨⟨visible,role⟩,_⟩
    rw [child_only d visible role]

theorem frontier_coverage (done : Nat → Prop) :
    (NoOverlap result reg interp (supported done) (tests done) root ∧
      CanGenerate result reg interp (supported done) (tests done) (Generated result reg interp (supported done)) root) ∧
    (NoOverlap result reg interp (supported done) (tests done) child ∧
      CanGenerate result reg interp (supported done) (tests done) (Generated result reg interp (supported done)) child) :=
  ⟨(coverage checked).mp ⟨_,root_selected done⟩,(coverage checked).mp ⟨_,child_selected done⟩⟩

theorem tree (done : Nat → Prop) : Classify (branch done) root (.selected dict) :=
  ⟨.selected impl.id [.selected leaf.id []],
    .selected (root_selected done) (.cons (.selected (child_selected done) .nil) .nil),
    .selected (.cons (.selected .nil (.selected rfl)) .nil) (.selected rfl)⟩

theorem declared : Declared reg root := by
  intro out requested
  cases List.mem_singleton.mp requested
  exact ⟨none,rfl⟩

theorem every_model (m) (valid : Models result m) : Evidence reg interp m root dict :=
  sound checked declared valid (tree (fun _ => False))

end Yulang.GeneralDeclarativeRepeatResolve327
