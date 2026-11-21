import Yulang.GeneralDeclarativeInlineGuards331
import Yulang.GeneralDeclarativeUnfinishedRoot330

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeInlineResult331
open GeneralDeclarativeInlineDecl331
open GeneralDeclarativeInlineFixture331
open GeneralDeclarativeInlineGuards331
open GeneralDeclarativeHiddenDecl324 (catalogue interpretation)
open GeneralDeclarativeHead320 (Models)
open GeneralDeclarativeStableCompiler329 (Frame)
open GeneralDeclarativeExampleSource320 (leaf)
open GeneralDeclarativeCurrentReceipt330 (Staged literal)
open GeneralDeclarativeUnfinishedRoot330 (Local59 dictionary_sound)
open GeneralDeclarativeEvidence320 (Evidence)
open GeneralDeclarativeOpaqueNominal328 (point point_bounded)
open GeneralDeclarativeClauseBatch327 (reflexive)
open CommonRoleOutermostResolver (Classify Dictionary)

abbrev dict : Dictionary := .node decl.id [.node leaf.id []]
abbrev branch (done : Nat → Prop) :=
  Local59 final registry interpretation (current done) (tests done) (Staged final registry interpretation)

def leafBase (_ : Nat) := point 3
def leafFrame : Frame final registry interpretation child leaf [] :=
  ⟨leafBase,[(0,point 3)],
    (by
      change GeneralDeclarativeStableReads329.Heads final catalogue interpretation [point 3] [.var 0] ([(0,point 3)] ++ [])
      exact .cons ⟨point_bounded _ 3,.variable 0,.variable 3,rfl,.refl _,.capture⟩ .nil),
    (by intro _ impossible; cases impossible),fun _ _ => point_bounded _ 3,
    targets,keep,final,final,[],rfl,reflexive final,[],rfl,fun _ impossible => False.elim (List.not_mem_nil impossible),
    [leafWrite],rfl,fun _ h => List.mem_append_right _ h,rfl⟩

theorem root_only (d) (registered : d ∈ registry.declarations) (role : d.role = root.role) : d = decl := by
  rcases List.mem_cons.mp registered with rfl|tail
  · rfl
  · cases List.mem_singleton.mp tail
    cases role

theorem child_only (d) (registered : d ∈ registry.declarations) (role : d.role = child.role) : d = leaf := by
  rcases List.mem_cons.mp registered with rfl|tail
  · cases role
  · exact List.mem_singleton.mp tail

theorem root_selected (done : Nat → Prop) : branch done root (.selected decl.id [child]) := by
  refine .prior (.selected (root_ready done) (safe done _) ?_
    ⟨⟨List.mem_cons_self,rfl⟩,root_matches done⟩ ?_ ⟨final,⟨frame⟩,literal (reflexive final)⟩)
  · rintro ⟨d,⟨visible,role⟩,wait⟩
    cases root_only d visible role
    exact wait (root_matches done)
  · rintro d ⟨⟨visible,role⟩,_⟩
    rw [root_only d visible role]

theorem child_selected (done : Nat → Prop) : branch done child (.selected leaf.id []) := by
  refine .prior (.selected (child_ready done) (safe done _) ?_
    ⟨⟨List.mem_cons_of_mem _ List.mem_cons_self,rfl⟩,child_matches done⟩ ?_ ⟨final,⟨leafFrame⟩,literal (reflexive final)⟩)
  · rintro ⟨d,⟨visible,role⟩,wait⟩
    cases child_only d visible role
    exact wait (child_matches done)
  · rintro d ⟨⟨visible,role⟩,_⟩
    rw [child_only d visible role]

theorem tree (done : Nat → Prop) : Classify (branch done) root (.selected dict) :=
  ⟨.selected decl.id [.selected leaf.id []],
    .selected (root_selected done) (.cons (.selected (child_selected done) .nil) .nil),
    .selected (.cons (.selected .nil (.selected rfl)) .nil) (.selected rfl)⟩

theorem all_models (_m : GeneralNominalCommonBridge.Assignment) (valid : Models final _m) :
    Evidence registry interpretation _m root dict :=
  dictionary_sound checked covered declared valid (tree (fun _ => False))

end Yulang.GeneralDeclarativeInlineResult331
