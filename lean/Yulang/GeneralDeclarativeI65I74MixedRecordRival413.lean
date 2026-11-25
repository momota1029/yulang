import Yulang.GeneralDeclarativeI65I74MixedRecordConservative413

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.MixedRecord413
open GeneralDeclarativeI65
open GeneralDeclarations (Declaration)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open CommonRoleOutermostResolver (Dictionary)

theorem PlainTape.actual_rival {s q d} {o : ActualOuterRecord s q} {rows}
    (tape : PlainTape o rows) (seen : d ∈ rows) : Nonempty (PlainCandidate o d) := by
  induction tape with
  | nil => cases seen
  | cons here _ ih =>
    rcases List.mem_cons.mp seen with same|later
    · cases same
      exact ⟨here⟩
    · exact ih later

theorem MixedTape.actual_rival {s q d} {o : ActualOuterRecord s q} {rows}
    (tape : MixedTape o rows) (i : Nat) (seen : rows[i]? = some d)
    (other : i ≠ tape.opening.ordinal) : Nonempty (PlainCandidate o d) := by
  induction tape generalizing i with
  | opens _ plain =>
    cases i with
    | zero => exact (other rfl).elim
    | succ n => exact plain.actual_rival (List.mem_of_getElem? (by simpa using seen))
  | @next first tail a t ih =>
    cases i with
    | zero =>
      have same : first = d := Option.some.inj seen
      exact ⟨same ▸ a⟩
    | succ n =>
      apply ih n (by simpa using seen)
      intro same
      apply other
      change n+1 = t.opening.ordinal+1
      rw [same]

/-- If one ignores election priority, a true binding-only rival has a
well-typed leaf payload in every fitting model. This theorem does not
create a SourceTrace or a Classifies result for the rival. -/
theorem actual_plain_rival_has_a_typed_leaf_payload413 {s q d} {o : ActualOuterRecord s q}
    (r : PlainCandidate o d) (seen : d ∈ visible s.core q)
    (m : I72.Model) (fit : Fits s m) :
    ∃ e : Event s q, e.frame.decl = d ∧ e.kids = [] ∧ LocalMeaning m e ∧
      FixedTargets m e ∧ DictionaryEvidence s m q (.node d.id []) := by
  have mem := ((visible_exact s.core q d).mp seen).1
  obtain ⟨ordinal, atSource⟩ := List.mem_iff_getElem?.mp mem
  let cap := plainCapture413 r
  let head := r.matches
  let frame : AuthoredBodyFrame393 s.core q :=
    ⟨ordinal,d,atSource,seen,unusedPlacement403,preoutputInputOfHead399 head cap⟩
  have never : ∀ i : Fin q.demand.outputs.length, False := by
    intro i
    have bad := i.isLt
    simp [o.noOutputs] at bad
  let event : Event s q := ⟨frame,head,fun i => (never i).elim⟩
  let source := node_from_exact_preoutput_head405 event r.checked cap rfl
  have interpreted := semantic_node_in_signature s q event source m fit
  have noKids : event.kids = [] := by
    simp [Event.kids,event,frame,frameWhereKids400,AuthoredBodyFrame393.clauses,children,r.noWhere]
  have fixed : FixedTargets m event := fun i => (never i).elim
  let kids : DictionaryEvidenceForest s m event.kids [] := noKids.symm ▸ .nil
  have original : DictionaryEvidence s m q (.node event.frame.decl.id []) :=
    .node event interpreted fixed kids
  exact ⟨event,rfl,noKids,interpreted,fixed,original⟩

/-- With genuine distinct binding matches, availability of a typed
rival payload and the actual K2 rejection coexist. The semantic
payload alone cannot select a rival and does not mask the diagnostic. -/
theorem every_matching_rival_has_payload_but_cannot_win413 {p : Checker408.Problem}
    (scan : MixedVerified p) (i : Nat) {d : Declaration}
    (rival : Rival413 scan.rejection i d)
    (m : I72.Model) (fit : Fits p.state m) :
    DictionaryEvidence p.state m p.root (.node d.id []) ∧
      ¬Classifies R5 p.state p.root (.selected (.node d.id [])) := by
  obtain ⟨plain⟩ := scan.rejection.tape.actual_rival i rival.1 rival.2.1
  obtain ⟨_,_,_,_,_,typed⟩ :=
    actual_plain_rival_has_a_typed_leaf_payload413 plain (List.mem_of_getElem? rival.1) m fit
  refine ⟨typed,?_⟩
  rintro ⟨t,e,⟨trace⟩,summary⟩
  rw [(actual_nested_K2_has_priority_over_every_R5_trace413 scan trace).1] at summary
  cases summary

end Yulang.GeneralDeclarativeI65.I72.MixedRecord413
