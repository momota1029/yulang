import Yulang.GeneralDeclarativeI65I74StructuralWhereBodyReplay428
import Yulang.GeneralDeclarativeI65I74StructuralWhereMixedAuditSupport430

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.StructuralWhere428
open I72.StructuralWhereMixedFixture430
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)

private def candidate428 : AuthoredCandidate mixedProblem.state.core mixedProblem.root frame.decl :=
  ⟨frame.inScope,by
    let env := mixedProblem.state.core.current.environment
    have roles : GeneralSourceMetadataRoles291.Valid env.source.roles :=
      (GeneralSourceMetadataRoles291.check_exact _).mp (by decide +kernel)
    have checked := (GeneralDeclarativeWitnessModeCoverage357.check_exact roles).mp (by decide +kernel)
    exact checked.1 _ (List.mem_of_getElem? frame.authored),
    checked_parent_syntax428.signature,rootPick.head⟩

private theorem only428 : visible mixedProblem.state.core mixedProblem.root = [frame.decl] := by
  decide +kernel

private def tape428 : CandidateTape mixedProblem.state.core mixedProblem.root
    (visible mixedProblem.state.core mixedProblem.root) :=
  only428.symm ▸ .next (.matched candidate428) .nil

private theorem tape_selected428 : TapedMatch mixedProblem.state.core mixedProblem.root tape428 frame.decl := by
  have same : ∀ rows (h : rows = [frame.decl]),
      let t : CandidateTape mixedProblem.state.core mixedProblem.root rows :=
        h.symm ▸ .next (.matched candidate428) .nil
      t.waits = false ∧ t.live = [frame.decl] := by
    intro rows h
    cases h
    exact ⟨rfl,rfl⟩
  exact ⟨rootPick.safe mixedProblem.state.b6,(same _ only428).1,(same _ only428).2⟩

theorem actual_singleton_tape_reaches_same_registry_row_and_lexical_capture428 :
    ∃ head : SelectedHeadOrigin395 (row:=frame.decl) tape428,
      let body := preoutputFrameOfOrigin399 head originalPlace (fun _ => I72.emptyCapture403)
      head.visibleOrdinal = 0 ∧ head.rawOrdinal = frame.ordinal ∧
        body.decl = frame.decl ∧
        body.input = rootPick.capture ∧
        (authoredRegistry mixedProblem.state.core.current).declarations[body.ordinal]? = some frame.decl := by
  obtain ⟨head⟩ := selected_head_original_origin395 tape_selected428
  have one : ∀ rows (h : rows = [frame.decl]),
      let t : CandidateTape mixedProblem.state.core mixedProblem.root rows :=
        h.symm ▸ .next (.matched candidate428) .nil
      storedCandidateEntries401 t = [(0,⟨frame.decl,candidate428⟩)] := by
    intro rows h
    cases h
    rfl
  have has := original_stored_entry_is_listed401 head.stored
  change (head.visibleOrdinal,⟨frame.decl,head.pick⟩) ∈ storedCandidateEntries401 tape428 at has
  unfold tape428 at has
  rw [one _ only428] at has
  obtain ⟨entry,stored⟩ := Prod.mk.inj (List.mem_singleton.mp has)
  have chosen := (eq_of_heq (Sigma.mk.inj stored).2 : head.pick = candidate428)
  have raw : head.rawOrdinal = frame.ordinal := by
    have original := head.ordinal
    rw [entry] at original
    have actual : unfilterOrdinal395
        (fun row : GeneralDeclarations.Declaration => row.role == mixedProblem.root.demand.role)
        (authoredRegistry mixedProblem.state.core.current).declarations 0 = some frame.ordinal := by
      decide +kernel
    exact Option.some.inj (original.symm.trans actual)
  refine ⟨head,entry,raw,rfl,?_,head.authored⟩
  change preoutputInputOfHead399 head.pick.head _ = rootPick.capture
  rw [chosen]
  change preoutputInputOfHead399 rootPick.head (fun _ => I72.emptyCapture403) = rootPick.capture
  have express := rootPick.sameCapture
  cases source : rootPick.head with
  | ordered captures _ =>
    rw [source] at express
    change captures = rootPick.capture
    change some captures = some rootPick.capture at express
    exact Option.some.inj express
  | joined _ =>
    rw [source] at express
    change none = some rootPick.capture at express
    cases express

#print axioms actual_singleton_tape_reaches_same_registry_row_and_lexical_capture428
end Yulang.GeneralDeclarativeI65.StructuralWhere428
