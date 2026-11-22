import Yulang.GeneralDeclarativeAlternativeEmbedding333
import Yulang.GeneralDeclarativeNestedReplayCases332

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 18000
set_option maxHeartbeats 14000000
namespace Yulang.GeneralDeclarativeAlternativeCurrentCase333
open GeneralDeclarativeHead320 (Models)
open GeneralDeclarativeAlternativeNeeds333 (Need finiteIndex Eventually Planned)
open GeneralDeclarativeAlternativeReplay333 (replay consume_current)
open GeneralDeclarativeAlternativeEmbedding333 (exact_replay)
open GeneralDeclarativeCurrentReceipt330 (literal)
open GeneralDeclarativeStableAttempt329 (Elected)
open GeneralDeclarativeNestedSiblingsFrame332 (source indexed keep parent childList targets final covered
  wanted_root grow_one grow_two)
open GeneralDeclarativeNestedSiblingsDecl332 (registry impl checked)
open GeneralDeclarativeNestedSiblingsResult332 (current tests root_selects root_only dictionary exact_tree every_model root_ready safe root_matches)
open GeneralDeclarativeNestedSiblingsModels332 (inhabited)
open GeneralDeclarativeNestedDecl332 (root)
open GeneralDeclarativeNestedExample332 (interpretation)
open GeneralDeclarativeNestedFrame332 (fallback)
open GeneralDeclarativeOpaqueNominal328 (point_bounded)
open GeneralDeclarativeGrowth327 (trans)
open GeneralDeclarativeEvidence320 (Evidence)
open GeneralDeclarativeStableCompiler329 (Frame)
open GeneralDeclarativeAssembly320 (Meaning)
open GeneralDeclarativeUnfinishedRoot330 (selected_old_exact)
open GeneralDeclarativeOpaqueBatch328 (check check_exact)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeOrigins321 (restriction)

theorem exact_members (done : Nat → Prop) :
    ∃ witness : List (Need (restriction (GeneralDeclarativeNestedSiblingsFrame332.origins done))),
      Eventually (fun fuel => (parent,childList) ∈
        replay (finiteIndex witness) fuel registry interpretation root impl source keep fallback targets) := by
  have fit : ∀ a ∈ root.arguments, Bounds (restriction (GeneralDeclarativeNestedSiblingsFrame332.origins done)) a := by
    intro a seen
    cases List.mem_singleton.mp seen
    exact point_bounded _ _
  exact (exact_replay (indexed done) fit (GeneralDeclarativeNestedReplayCases332.actual_replay done)).finite

theorem elected_now (done : Nat → Prop) :
    Elected final registry interpretation (current done) (tests done) root impl := by
  refine ⟨root_ready done,safe done _,?_,⟨⟨List.mem_cons_self,rfl⟩,root_matches done⟩,?_⟩
  · rintro ⟨d,⟨visible,role⟩,waiting⟩
    cases root_only d visible role
    exact waiting (root_matches done)
  · intro actual shape
    rw [root_only actual shape.1.1 shape.1.2]

theorem actual_receipt (done : Nat → Prop) :
    ∃ frame : Frame parent registry interpretation root impl childList,
      frame.targets = targets ∧
      (∀ m, Models final m → Meaning registry interpretation m root impl frame.capture childList) := by
  obtain ⟨packet,fuel,ready⟩ := exact_members done
  have fit : ∀ a ∈ root.arguments, Bounds source a := by
    intro a seen
    cases List.mem_singleton.mp seen
    exact point_bounded _ _
  obtain ⟨frame,names,_,_,meaning⟩ := consume_current (finiteIndex packet) checked covered
    wanted_root fit (ready fuel (Nat.le_refl fuel)) (literal (trans grow_one grow_two))
    (elected_now done) (check_exact.mpr rfl)
  exact ⟨frame,names,meaning⟩

theorem real_current_dictionary :
    ∃ frame : Frame parent registry interpretation root impl childList,
      frame.targets = targets ∧
      ∃ m, Models final m ∧ Meaning registry interpretation m root impl frame.capture childList ∧
        Evidence registry interpretation m root dictionary := by
  obtain ⟨frame,kept,meaning⟩ := actual_receipt (fun _ => False)
  obtain ⟨m,fit⟩ := inhabited
  exact ⟨frame,kept,m,fit,meaning m fit,every_model m fit⟩

end Yulang.GeneralDeclarativeAlternativeCurrentCase333
