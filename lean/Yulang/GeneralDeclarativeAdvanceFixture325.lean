import Yulang.GeneralDeclarativeSourceFixture325
import Yulang.GeneralDeclarativeSourceAdvance325

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeAdvanceFixture325
open GeneralDeclarativeHiddenDecl324
open GeneralDeclarativeHiddenState324
open GeneralDeclarativeHiddenStages324 (Stage candidate root_ready' leaf_ready' no_recurs tested_root tested_leaf)
open GeneralDeclarativeHiddenStageReads324 (selected_parent selected_child)
open GeneralDeclarativeHiddenResolve324 (dictionary root_only child_only)
open GeneralDeclarativeHiddenReads324 (declared_root)
open GeneralDeclarativeExampleSource320 (leaf)
open GeneralDeclarativeHead320 (Models)
open GeneralDeclarativeFrameReadback325 (Recorded)
open GeneralDeclarativeSourceFixture325 (base placement root_frame child_frame root_emits leaf_emits whole_evidence)
open GeneralDeclarativeSourceAdvance325 (Rule selected_application after_ordinary)
open GeneralDeclarativeSourceSelection325 (map_generated)
open GeneralDeclarativeEvidence320 (Evidence)

abbrev branch (phase : Stage) (done : Nat → Prop) :=
  Rule phase.ordinary registry interpretation (phase.equations done) (candidate phase done)

theorem first_choice (done : Nat → Prop) : branch .initial done root (.selected parent.id [child]) := by
  refine .selected (root_ready' .initial done) (no_recurs .initial done _) ?_
    ⟨⟨List.mem_cons_self,rfl⟩,tested_root .initial done⟩ ?_
    ⟨base,placement,root_frame .initial done,root_emits,[parentRow],rfl⟩
  · rintro ⟨d,⟨vis,role⟩,block⟩
    cases root_only d vis role
    exact block (tested_root .initial done)
  · rintro d ⟨⟨vis,role⟩,_⟩
    rw [root_only d vis role]

theorem second_choice (done : Nat → Prop) :
    branch .parentWritten done child (.selected leaf.id []) := by
  refine .selected (leaf_ready' .parentWritten done) (no_recurs .parentWritten done _) ?_
    ⟨⟨List.mem_cons_of_mem _ List.mem_cons_self,rfl⟩,tested_leaf .parentWritten done⟩ ?_
    ⟨base,placement,child_frame .parentWritten done,leaf_emits,[childRow],rfl⟩
  · rintro ⟨d,⟨vis,role⟩,block⟩
    cases child_only d vis role
    exact block (tested_leaf .parentWritten done)
  · rintro d ⟨⟨vis,role⟩,_⟩
    rw [child_only d vis role]

theorem first_recording (done : Nat → Prop) :
    Recorded afterParent registry interpretation (Stage.equations .parentWritten done)
      root parent base placement :=
  after_ordinary (root_frame .initial done) (rows := [parentRow]) rfl 1

theorem second_recording (done : Nat → Prop) :
    Recorded final registry interpretation (Stage.equations .bothWritten done)
      child leaf base placement :=
  after_ordinary (child_frame .parentWritten done) (rows := [childRow]) rfl 2

theorem composed_actual :
    branch .initial (fun _ => False) root (.selected parent.id [child]) ∧
    branch .parentWritten (fun _ => False) child (.selected leaf.id []) ∧
    (∀ m, Models final m ↔ Models initial m ∧ GeneralDeclarativeEntailment320.Holds m parentRow ∧
      GeneralDeclarativeEntailment320.Holds m childRow) ∧
    ∀ m, Models final m → Evidence registry interpretation m root dictionary :=
  ⟨first_choice _,second_choice _,final_models,whole_evidence⟩

end Yulang.GeneralDeclarativeAdvanceFixture325
