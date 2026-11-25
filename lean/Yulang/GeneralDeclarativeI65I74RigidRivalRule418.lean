import Yulang.GeneralDeclarativeI65I74RigidRivalSource418

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RigidRival418
open GeneralDeclarativeI65
open CommonRoleOutermostResolver (All₂ Dictionary Summarizes Result)
open GeneralDeclarations (Declaration)
open X6Ambiguous417 (PlainHit Visits)
open PlainMerged416 (PlainRows)

structure Winner (s : I72.State) (q : I72.Request) where
  rows : PlainRows s q
  winner : PlainHit rows
  mismatch : RigidMismatch rows
  ordered : visible s.core q = [winner.candidate.decl,mismatch.rival.candidate.decl] ∨
    visible s.core q = [mismatch.rival.candidate.decl,winner.candidate.decl]
  distinct : winner.candidate.decl.id ≠ mismatch.rival.candidate.decl.id
  inspections : Visits rows

theorem actual_candidates_and_no_others418 {s q} (shape : Winner s q) (d : Declaration) :
    d ∈ visible s.core q ↔
      d = shape.winner.candidate.decl ∨ d = shape.mismatch.rival.candidate.decl := by
  rcases shape.ordered with h|h <;> rw [h] <;> simp [or_comm]

theorem exact_winner_has_no_where418 {s q} (a : Winner s q) : a.winner.event.kids = [] := by
  simp [Event.kids,frameWhereKids400,children,AuthoredBodyFrame393.clauses,PlainHit.event,
    X6Ambiguous417.Candidate.frame,a.winner.candidate.noWhere]

inductive ExactWinner (s : I72.State) : (q : I72.Request) → Event s q → Type where
  | actual {q} (a : Winner s q) : ExactWinner s q a.winner.event

def R10 : SourcePrimitives where
  elected := fun s q e needs => X6Ambiguous417.R9.elected s q e needs ∨
    needs = [] ∧ Nonempty (ExactWinner s q e)
  other := X6Ambiguous417.R9.other

theorem selected_rigid_local_sound418 {s q e needs}
    (sound : R10.elected s q e needs) (m : I72.Model) (fit : Fits s m) :
    LocalMeaning m e ∧ FixedTargets m e := by
  rcases sound with old|new
  · exact PlainMerged416.selected_plain_local_sound416 old m fit
  · obtain ⟨data⟩ := new.2
    cases data with
    | actual winner =>
      refine ⟨⟨source_head_sound winner.winner.event.head m fit,?_⟩,?_⟩ <;>
        (intro i; have h := i.isLt; simp [winner.rows.noOutputs] at h)

theorem selected_trace_is_dictionary_sound418 {s q t e} (trace : SourceTrace R10 s q t e)
    (m : I72.Model) (fit : Fits s m) :
    ∀ d, Summarizes t (.selected d) → DictionaryEvidence s m q d := by
  exact SourceTrace.rec (R := R10) (s := s)
    (motive_1 := fun q t _ _ => ∀ d, Summarizes t (.selected d) → DictionaryEvidence s m q d)
    (motive_2 := fun qs ts _ => ∀ ds, All₂ Summarizes ts (ds.map Result.selected) →
      DictionaryEvidenceForest s m qs ds)
    (motive_3 := fun _ _ => True)
    (fun _ _ evidence => by cases evidence)
    (fun v _ _ _ _ _ evidence => by cases v <;> cases evidence)
    (fun event _ decision _ _ _ proveKids d actual => by
      have semantics := selected_rigid_local_sound418 decision m fit
      cases actual with
      | selected ordered combine =>
        cases combine with
        | selected exactEach =>
          rw [exactEach] at ordered
          exact .node event semantics.1 semantics.2 (proveKids _ ordered))
    (fun ds pair => by
      cases ds with
      | nil => exact .nil
      | cons => cases pair)
    (fun _ _ first rest ds ordered => by
      cases ds with
      | nil => cases ordered
      | cons d ds =>
        cases ordered with
        | cons head tail => exact .cons (first d head) (rest ds tail))
    True.intro (fun _ _ _ _ _ _ => True.intro) trace

theorem dictionary_sound_R10 : DictionarySound R10 := by
  rintro s q d ⟨t,e,⟨trace⟩,result⟩ m fit
  exact selected_trace_is_dictionary_sound418 trace m fit d result

end Yulang.GeneralDeclarativeI65.I72.RigidRival418
