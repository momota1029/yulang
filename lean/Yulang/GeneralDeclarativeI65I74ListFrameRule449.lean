import Yulang.GeneralDeclarativeI65I74ListFrameChoice449

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.ListSites449.Frame
open Yulang.GeneralDeclarativeI65
open Checker408 (Problem Result)
open GeneralDeclarations (Declaration)
open GeneralDeclarativeWitnessDeclaredState357 (point)

structure FramedSelection (p : Problem) where
  decl : Declaration
  chosen : ListFrameChoice p decl

def FramedSelection.report {p} (a : FramedSelection p) : Result :=
  Check408.nullaryReport a.decl

def selectedFrameEvent {p : Problem} (a : FramedSelection p)
    (origin : SelectedHeadOrigin395 (row := a.decl) a.chosen.tape) : Event p.state p.root :=
  ⟨preoutputFrameOfOrigin399 origin unusedPlacement403 (fun _ => emptyCapture403),
    origin.pick.head, fun i => (by
      have notPresent := i.isLt
      simp [a.chosen.noOutputs] at notPresent : False).elim⟩

/-- Independent no-output rule on the same selected declaration, with
all of the actual ordered authored input heads and root safety. -/
def listFrameRule : SourcePrimitives where
  elected := fun s q e needs => needs = [] ∧ ∃ a : FramedSelection ⟨s,q⟩,
    ∃ source : SelectedHeadOrigin395 (row := a.decl) a.chosen.tape,
      e = selectedFrameEvent a source
  other := fun _ _ _ _ => False

theorem original_picked_frame_is_chosen_source449 {p} (a : FramedSelection p)
    (origin : SelectedHeadOrigin395 (row := a.decl) a.chosen.tape) :
    origin.pick = a.chosen.candidate := by
  have shape : ∀ rows (xs : rows = [a.decl]),
      let t : CandidateTape p.state.core p.root rows := xs.symm ▸ .next (.matched a.chosen.candidate) .nil
      storedCandidateEntries401 t = [(0,⟨a.decl,a.chosen.candidate⟩)] := by
    intro rows xs
    cases xs
    rfl
  have atSource := original_stored_entry_is_listed401 origin.stored
  change (origin.visibleOrdinal,⟨a.decl,origin.pick⟩) ∈
      storedCandidateEntries401 a.chosen.tape at atSource
  unfold ListFrameChoice.tape at atSource
  rw [shape _ a.chosen.only] at atSource
  exact eq_of_heq (Sigma.mk.inj (congrArg Prod.snd (List.mem_singleton.mp atSource))).2

theorem same_frame_binders_reach_original_event449 {p} (a : FramedSelection p)
    (origin : SelectedHeadOrigin395 (row := a.decl) a.chosen.tape) :
    ∀ b u, (b,u) ∈ a.chosen.roster.bindings → (selectedFrameEvent a origin).frame.input b = point u := by
  intro b u remembered
  change preoutputInputOfHead399 origin.pick.head (fun _ => emptyCapture403) b = point u
  rw [original_picked_frame_is_chosen_source449 a origin]
  exact frame_lookup_preserves_original_capture449 a.chosen.roster a.chosen.distinct remembered

theorem exact_framed_selection_assembly449 {p : Problem} (a : FramedSelection p) :
    ∃ e : Event p.state p.root,
      Nonempty (SourceTrace listFrameRule p.state p.root a.report.tree (some e)) ∧
      a.report.writes = Check408.encodedEventWrites e ∧
      (∀ b u, (b,u) ∈ a.chosen.roster.bindings → e.frame.input b = point u) ∧
      ∀ m, I72.Fits p.state m → I72.DictionaryEvidence p.state m p.root (.node a.decl.id []) := by
  obtain ⟨source⟩ := selected_head_original_origin395
    (actual_single_declaration_list_frame_is_settled449 a.chosen)
  let e := selectedFrameEvent a source
  have noKids : e.kids = [] := by
    simp [e,selectedFrameEvent,Event.kids,frameWhereKids400,AuthoredBodyFrame393.clauses,
      preoutputFrameOfOrigin399,frameAtSource395,a.chosen.noWhere,children]
  have localRule : listFrameRule.elected p.state p.root e [] := ⟨rfl,a,source,rfl⟩
  have leaves : WhereForest listFrameRule p.state e.kids [] := noKids ▸ .nil
  let trace : SourceTrace listFrameRule p.state p.root a.report.tree (some e) :=
    .selected e a.chosen.safe localRule .nil leaves
  refine ⟨e,⟨trace⟩,?_,same_frame_binders_reach_original_event449 a source,?_⟩
  · exact (List.length_eq_zero_iff.mp (by simp [Check408.encodedEventWrites,a.chosen.noOutputs])).symm
  · intro m fit
    have node : GeneralNode e := node_from_exact_preoutput_head405 _ a.chosen.checked
      (fun _ => emptyCapture403) rfl
    have own : FixedTargets m e := by
      intro i
      have missing := i.isLt
      simp [a.chosen.noOutputs] at missing
    have empty : DictionaryEvidenceForest p.state m e.kids [] := noKids ▸ .nil
    exact .node e (semantic_node_in_signature _ _ e node m fit) own empty

end Yulang.GeneralDeclarativeI65.I72.ListSites449.Frame
