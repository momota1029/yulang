import Yulang.GeneralDeclarativeI65I74OpaqueRosterRead448

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.Opaque448.Roster
open Yulang.GeneralDeclarativeI65
open Checker408 (Problem Result)
open GeneralDeclarations (Declaration)
open RetainedFull445

structure WholeChoice (p : Problem) where
  point : VerifiedPoint p
  roster : BareRows p.state.core (visible p.state.core p.root)
  picked : Declaration
  only : roster.living point.known.key = [picked]
  noOutputs : p.root.demand.outputs = []
  authoredRole : ∃ row ∈ p.state.core.current.environment.source.roles.rows,
    row.role = p.root.demand.role

def WholeChoice.report {p} (a : WholeChoice p) : Result :=
  Check408.nullaryReport a.picked

def readWholeChoice (p : Problem) (w : NamedWire) : Option (WholeChoice p) := do
  if role : (Checker408.originalRole p).isSome = true then
    if out : p.root.demand.outputs.isEmpty = true then
      let a ← readBarePoint p w
      let roster ← readBareRows p.state.core (visible p.state.core p.root)
      match only : roster.living a.known.key with
      | [picked] =>
        have authored : ∃ row ∈ p.state.core.current.environment.source.roles.rows,
            row.role = p.root.demand.role := by
          cases hit : Checker408.originalRole p with
          | none => simp [hit] at role
          | some row =>
            have actual := GeneralSourceMetadataRoles291.indexed hit
            exact ⟨row,actual.1,actual.2⟩
        some ⟨a,roster,picked,only,List.isEmpty_iff.mp out,authored⟩
      | _ => none
    else none
  else none

theorem whole_choice_has_exact_replay448 {p : Problem} (a : WholeChoice p) :
    ∃ w, readWholeChoice p w = some a := by
  obtain ⟨w,atPoint⟩ := independent_bare_point_has_finite_wire448 a.point
  refine ⟨w,?_⟩
  have role := original_role_is_read448 a.authoredRole (p := p)
  have out : p.root.demand.outputs.isEmpty = true := by simp [a.noOutputs]
  unfold readWholeChoice
  rw [dite_eq_left role,dite_eq_left out]
  simp only [atPoint,read_bare_roster_exact448 a.roster,Bind.bind,Option.bind]
  split
  · rename_i d only
    have eq := List.singleton_inj.mp (only.symm.trans a.only)
    subst d
    rfl
  · rename_i other
    exact (other _ a.only).elim

private theorem BareRows.member_row {s rows} (a : BareRows s rows)
    {d : Declaration} (member : d ∈ rows) : Nonempty (BareRow s d) := by
  induction a with
  | nil => cases member
  | next first tail ih =>
    rcases List.mem_cons.mp member with equal|rest
    · subst d
      exact ⟨first⟩
    · exact ih rest

def WholeChoice.tape {p} (a : WholeChoice p) : CandidateTape p.state.core p.root (visible p.state.core p.root) :=
  a.roster.tape a.point.known (fun _ inScope => inScope)

theorem whole_choice_is_only_settled_actual_match448 {p} (a : WholeChoice p) :
    TapedMatch p.state.core p.root a.tape a.picked :=
  actual_whole_bare_single_match_selects448 a.point.known a.roster a.point.safe a.only

/-- Exact selected event independently ties the selected declaration to
the whole scope tape, its original ordinal, preoutput head and placement.
The output callback is vacuous on this no-output local rule. -/
def wholeEvent {p : Problem} (a : WholeChoice p)
    (origin : SelectedHeadOrigin395 (row := a.picked) a.tape) : Event p.state p.root :=
  ⟨preoutputFrameOfOrigin399 origin unusedPlacement403 (fun _ => emptyCapture403),
    origin.pick.head,fun i => (by
      have bad := i.isLt
      simp [a.noOutputs] at bad : False).elim⟩

def wholeRule : SourcePrimitives where
  elected := fun s q e needs => needs = [] ∧ ∃ a : WholeChoice ⟨s,q⟩,
    ∃ origin : SelectedHeadOrigin395 (row := a.picked) a.tape, e = wholeEvent a origin
  other := fun _ _ _ _ => False

theorem whole_event_has_no_kids448 {p} (a : WholeChoice p)
    (origin : SelectedHeadOrigin395 (row := a.picked) a.tape) :
    (wholeEvent a origin).kids = [] := by
  obtain ⟨row⟩ := a.roster.member_row origin.pick.inScope
  simp [wholeEvent,Event.kids,frameWhereKids400,AuthoredBodyFrame393.clauses,
    preoutputFrameOfOrigin399,frameAtSource395,row.noWhere,children]

theorem whole_event_fixed_targets448 {p} (a : WholeChoice p)
    (origin : SelectedHeadOrigin395 (row := a.picked) a.tape) (m : I72.Model) :
    FixedTargets m (wholeEvent a origin) := by
  intro i
  have impossible := i.isLt
  simp [a.noOutputs] at impossible

theorem whole_event_node448 {p} (a : WholeChoice p)
    (origin : SelectedHeadOrigin395 (row := a.picked) a.tape) :
    GeneralNode (wholeEvent a origin) := by
  obtain ⟨row⟩ := a.roster.member_row origin.pick.inScope
  exact node_from_exact_preoutput_head405 _ row.checked (fun _ => emptyCapture403) rfl

theorem whole_choice_assembly448 {p : Problem} (a : WholeChoice p) :
    ∃ e : Event p.state p.root,
      Nonempty (SourceTrace wholeRule p.state p.root a.report.tree (some e)) ∧
      a.report.writes = Check408.encodedEventWrites e ∧
      ∀ m, I72.Fits p.state m → I72.DictionaryEvidence p.state m p.root (.node a.picked.id []) := by
  obtain ⟨origin⟩ := selected_head_original_origin395 (whole_choice_is_only_settled_actual_match448 a)
  let e := wholeEvent a origin
  have noKids : e.kids = [] := whole_event_has_no_kids448 a origin
  have prior : wholeRule.elected p.state p.root e [] := ⟨rfl,a,origin,rfl⟩
  have leaves : WhereForest wholeRule p.state e.kids [] := noKids ▸ .nil
  let trace : SourceTrace wholeRule p.state p.root a.report.tree (some e) :=
    .selected e a.point.safe prior .nil leaves
  refine ⟨e,⟨trace⟩,?_,?_⟩
  · exact (List.length_eq_zero_iff.mp (by simp [Check408.encodedEventWrites,a.noOutputs])).symm
  · intro m fit
    have meaning : LocalMeaning m e :=
      semantic_node_in_signature _ _ e (whole_event_node448 a origin) m fit
    have empty : DictionaryEvidenceForest p.state m e.kids [] := noKids ▸ .nil
    exact .node e meaning (whole_event_fixed_targets448 a origin m) empty

end Yulang.GeneralDeclarativeI65.I72.Opaque448.Roster
