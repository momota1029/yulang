import Yulang.GeneralDeclarativeI65I74StructuralWhereBodyReplay428
import Yulang.GeneralDeclarativeI65I74StructuralWhereMixedAuditSupport430

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.StructuralWhere428
open GeneralDeclarations (Declaration)
open I72.StructuralWhereMixedFixture430

private def oneVisibleTape428 {s q d} (candidate : AuthoredCandidate s q d)
    (only : visible s q = [d]) : CandidateTape s q (visible s q) :=
  only.symm ▸ .next (.matched candidate) .nil

private theorem oneVisibleTapeExact428 {s q d} (candidate : AuthoredCandidate s q d)
    (only : visible s q = [d]) (raw : ¬ GeneralDeclarativePriority321.RootRecurs s.current.ordinary q.demand) :
    TapedMatch s q (oneVisibleTape428 candidate only) d := by
  have actual : ∀ rows (eq : rows = [d]),
      let t : CandidateTape s q rows := eq.symm ▸ .next (.matched candidate) .nil
      t.waits = false ∧ t.live = [d] := by
    intro rows eq; cases eq; exact ⟨rfl,rfl⟩
  exact ⟨raw,(actual _ only).1,(actual _ only).2⟩

private theorem original_decl_covered428 (d : Declaration)
    (decl : d ∈ mixedProblem.state.core.current.environment.source.declarations) :
    GeneralDeclarativeWitnessModeCoverage357.DeclarationCovered
      mixedProblem.state.core.current.environment d := by
  let env := mixedProblem.state.core.current.environment
  have roles : GeneralSourceMetadataRoles291.Valid env.source.roles :=
    (GeneralSourceMetadataRoles291.check_exact _).mp (by decide +kernel)
  have coverage := (GeneralDeclarativeWitnessModeCoverage357.check_exact roles).mp (by decide +kernel)
  exact coverage.1 d decl

theorem actual_original_singleton_parent_and_structural_child_fit_the_current_tape428 :
    (∃ t : CandidateTape mixedProblem.state.core mixedProblem.root
        (visible mixedProblem.state.core mixedProblem.root),
        TapedMatch mixedProblem.state.core mixedProblem.root t frame.decl) ∧
    (∃ t : CandidateTape mixedProblem.state.core actualRecord.child
        (visible mixedProblem.state.core actualRecord.child),
        TapedMatch mixedProblem.state.core actualRecord.child t selectedStruct.source.decl) := by
  have rootOnly : visible mixedProblem.state.core mixedProblem.root = [frame.decl] := by decide +kernel
  let parent : AuthoredCandidate mixedProblem.state.core mixedProblem.root frame.decl :=
    ⟨frame.inScope,original_decl_covered428 _ (List.mem_of_getElem? frame.authored),
      checked_parent_syntax428.signature,rootPick.head⟩
  let child : AuthoredCandidate mixedProblem.state.core actualRecord.child selectedStruct.source.decl :=
    ⟨by simp [selectedStruct.source.only],
      original_decl_covered428 _ (List.mem_of_getElem? selectedStruct.source.authored),
      selectedStruct.source.checked.signature,selectedStruct.source.sourceHead⟩
  exact ⟨⟨_,oneVisibleTapeExact428 parent rootOnly (rootPick.safe mixedProblem.state.b6)⟩,
    ⟨_,oneVisibleTapeExact428 child selectedStruct.source.only selectedStruct.rawSafe⟩⟩

#print axioms actual_original_singleton_parent_and_structural_child_fit_the_current_tape428
end Yulang.GeneralDeclarativeI65.StructuralWhere428
