import Yulang.GeneralDeclarativeAlternateNames327
import Yulang.GeneralDeclarativeFrontierView327
import Yulang.GeneralDeclarativePlacementEvidence327

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 14000
namespace Yulang.GeneralDeclarativeRelation327
open GeneralDeclarativeRepeatDecl327
open GeneralDeclarativeRepeatState327
open GeneralDeclarativeRepeatProbe327
open GeneralDeclarativeRepeatGraph327 (safe)
open GeneralDeclarativeRepeatFrame327
open GeneralDeclarativeRepeatResolve327
open GeneralDeclarativeAlternateNames327
open GeneralDeclarativeProjectedFrame326 (Generated)
open GeneralDeclarativeFrontierView327 (ExactInputs)
open GeneralDeclarativeHead320 (Models)
open GeneralDeclarativePlacementEquiv327 (RequestSame complete_ordered)
open GeneralDeclarativePlacementEvidence327 (retarget)
open GeneralDeclarativeAssembly320 (Node)
open GeneralDeclarativeEvidence320 (Evidence)
open GeneralDeclarativeExampleSource320 (leaf)
open CommonRoleOutermostResolver (All₂)

/-- Even exact flags for this well-formed source cannot make a function
whose literal child vectors exactly enumerate the unrefined relation. -/
theorem no_functional_view (done : Nat → Prop) :
    ¬∃ hasLower recursive passes waiting produce, ExactInputs result reg interp (supported done)
      (tests done) root (Generated result reg interp (supported done)) hasLower recursive passes waiting produce := by
  rintro ⟨_,_,_,_,produce,fields⟩
  have clear : ¬GeneralDeclarativePriority321.Blocked reg (tests done) root := by
    rintro ⟨d,⟨reg,role⟩,notMatch⟩
    cases root_only d reg role
    exact notMatch (root_matches done)
  have one : GeneralDeclarativeFrontier327.Unique reg (tests done) root impl := by
    refine ⟨⟨⟨List.mem_cons_self,rfl⟩,root_matches done⟩,?_⟩
    intro rival chosen
    rw [root_only rival chosen.1.1 chosen.1.2]
  exact no_literal_producer done ⟨produce impl,
    fields.generation (root_support done) (safe done root) clear impl one⟩

theorem same_ports (m) (valid : Models result m) :
    All₂ (RequestSame m) [child] [alternate] := by
  have comparison := complete_ordered (left := place) (right := alternatePlace) (base := base)
    rfl (parent_frame (fun _ => False)).clauses (alternate_parent (fun _ => False)).clauses m valid
  rwa [emitted,alternate_emits] at comparison

theorem transport_actual_tree (m) (valid : Models result m)
    (checkedParent : Node reg interp m root impl.id [child])
    (checkedChildren : All₂ (Evidence reg interp m) [child] [.node leaf.id []]) :
    Node reg interp m root impl.id [alternate] ∧
      All₂ (Evidence reg interp m) [alternate] [.node leaf.id []] :=
  retarget (same_ports m valid) checkedParent checkedChildren

end Yulang.GeneralDeclarativeRelation327
