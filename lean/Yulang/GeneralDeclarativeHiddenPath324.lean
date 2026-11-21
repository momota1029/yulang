import Yulang.GeneralDeclarativeHiddenStageReads324
import Yulang.GeneralDeclarativeApplyAssoc324

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeHiddenPath324
open GeneralDeclarativeHiddenDecl324
open GeneralDeclarativeHiddenState324
open GeneralDeclarativeHiddenStages324 (Stage localRule)
open GeneralDeclarativeHiddenStageReads324 (read_parent read_child selected_parent selected_child)
open GeneralDeclarativeHiddenReads324 (declared_root declared_child body_root body_child)
open GeneralDeclarativeHiddenResolve324 (dictionary branch final_selected final_evidence)
open GeneralDeclarativeApplyAssoc324 (Applies effect closure)
open GeneralDeclarativeModelStable324 (StableUnder stable_exact)
open GeneralDeclarativeAssocRule323 (SourceEquation)
open GeneralDeclarativeHead320 (Models)
open GeneralDeclarativeEntailment320 (Holds)
open GeneralDeclarativeEvidence320 (Evidence)
open GeneralDeclarativeExampleSource320 (leaf)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (Classify)

theorem parent_event :
    Applies initial registry interpretation (localRule .initial (fun _ => False))
      root parent names place [parentRow] :=
  ⟨List.mem_cons_self,rfl,(by rw [exact_child]; exact selected_parent .initial _),
    read_parent .initial,declared_root,body_root,root_rule⟩

theorem child_event :
    Applies afterParent registry interpretation (localRule .parentWritten (fun _ => False))
      child leaf leafNames place [childRow] :=
  ⟨List.mem_cons_of_mem _ List.mem_cons_self,rfl,selected_child .parentWritten _,
    read_child .parentWritten,declared_child,body_child,child_rule⟩

theorem root_is_stable_after_parent :
    StableUnder afterParent (SourceEquation registry interpretation root parent names.input) :=
  closure checked parent_event

theorem child_is_stable_after_child :
    StableUnder final (SourceEquation registry interpretation child leaf leafNames.input) :=
  closure checked child_event

/-- State effect of the two actual applications, in their original
source order. The selected final branch is checked separately. -/
theorem actual_effect (m : Assignment) :
    Models final m ↔ Models initial m ∧
      (∀ e, SourceEquation registry interpretation root parent names.input e → Holds m e) ∧
      (∀ e, SourceEquation registry interpretation child leaf leafNames.input e → Holds m e) := by
  rw [show Models final m ↔ Models afterParent m ∧ _ from effect checked child_event m,
    show Models afterParent m ↔ Models initial m ∧ _ from effect checked parent_event m,
    and_assoc]

theorem full_source_path :
    Applies initial registry interpretation (localRule .initial (fun _ => False)) root parent names place [parentRow] ∧
    Applies afterParent registry interpretation (localRule .parentWritten (fun _ => False)) child leaf leafNames place [childRow] ∧
    Classify (branch (fun _ => True)) root (.selected dictionary) ∧
    Models final (assignment true) ∧
    (∀ m, Models final m → Evidence registry interpretation m root dictionary) :=
  ⟨parent_event,child_event,final_selected _,fits_final,final_evidence⟩

end Yulang.GeneralDeclarativeHiddenPath324
