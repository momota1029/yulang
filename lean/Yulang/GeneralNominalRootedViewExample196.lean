import Yulang.GeneralNominalRootedView196
import Yulang.GeneralNominalViewExample196

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalRootedViewExample196
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalViewTransport196
open GeneralNominalViewExample196 (before next declaration variable_query)
open GeneralNominalRootedView196

abbrev nominal : Declaration := ⟨901,0,[.app 0 [.var 0]],[],[],[]⟩
abbrev registry : Registry := ⟨GeneralDeclarationExamples.constructors,
  GeneralDeclarationExamples.roles,[declaration,nominal]⟩
abbrev root := GeneralNominalExamples.displayRoot
abbrev tree : Dictionary GeneralDeclarationExamples.roles := .node root 900 []

theorem supported : Support registry before next tree := by
  apply Support.node
  · apply node_of_variables
    intro decl member identity
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact ⟨[[0]],variable_query⟩
    · cases identity
  · intro child member; cases member

abbrev bounds : List (GeneralNominalInspection.Bounds before.state) := [(0,0)]

theorem not_global : ¬ Rechecks registry before next := by
  intro global
  have same := global nominal (by simp) bounds
  have blocked := congrArg GeneralNominalRecursiveInspection.Report.blocked same
  have different : (GeneralNominalRecursiveCandidates.report (context before next) nominal bounds).blocked ≠
      (report next (GeneralNominalRecursiveCandidates.report before nominal bounds)).blocked := by
    decide +kernel
  exact different blocked
end Yulang.GeneralNominalRootedViewExample196
