import Yulang.GeneralDeclarativeI65I74PlainMergedReport416
import Yulang.GeneralDeclarativeI65I74PlainMergedReplay416

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.PlainMerged416
open GeneralDeclarativeI65
open CommonRoleOutermostResolver (Summarizes)
open Checker408 (Problem Result)

theorem exact_plain_merge_has_selected_report416 {p : Problem} (a : VerifiedPlain p) :
    ClassifiedAs p.state p.root (Check408.nullaryReport a.actual.candidate.decl) := by
  let event := a.actual.event
  let noneKids : WhereForest R8 p.state event.kids [] :=
    (actual_plain_event_has_no_where416 a.actual).symm ▸ (.nil : WhereForest R8 p.state [] [])
  let original : SourceTrace R8 p.state p.root
      (.selected a.actual.candidate.decl.id []) (some event) :=
    .selected event a.rootSafe (.inr ⟨rfl,⟨.actual a.rows a.actual⟩⟩) .nil noneKids
  have noWrites : Check408.encodedEventWrites event = [] :=
    List.length_eq_zero_iff.mp (by simp [Check408.encodedEventWrites,a.rows.noOutputs])
  have noneWrites : ∀ qs (h : qs = []),
      forestWrites (h.symm ▸ (.nil : WhereForest R8 p.state [] [])) = [] := by
    intro qs h
    cases h
    rfl
  have same : writes original = [] := by
    change Check408.encodedEventWrites event ++ forestWrites noneKids = []
    have none := noneWrites _ (actual_plain_event_has_no_where416 a.actual)
    rw [noWrites,none]
    rfl
  exact ⟨some event,original,.selected .nil (.selected rfl),same.symm⟩

inductive Witness where
  | previous (old : ClosedResidual415.Witness)
  | plainMerged (w : PlainWire)
  | unsupported

def check (p : Problem) (r : Result) : Witness → Bool
  | .previous old => ClosedResidual415.check p r old
  | .plainMerged w =>
    match replayPlain416 p w with
    | none => false
    | some a =>
      let verdict := Check408.nullaryReport a.actual.candidate.decl
      Check408.matchesNoWrites r verdict.tree verdict.verdict
  | .unsupported => false

theorem previous_entry_unchanged416 (p : Problem) (r : Result) (w : ClosedResidual415.Witness) :
    check p r (.previous w) = ClosedResidual415.check p r w := rfl

theorem checked_plain_merge_reflects_original416 (p : Problem) (r : Result) (w : PlainWire)
    (yes : check p r (.plainMerged w) = true) :
    ∃ v, replayPlain416 p w = some v ∧ r = Check408.nullaryReport v.actual.candidate.decl := by
  cases seen : replayPlain416 p w with
  | none => simp [check,seen] at yes
  | some a =>
    have result : Check408.matchesNoWrites r (Check408.nullaryReport a.actual.candidate.decl).tree
        (Check408.nullaryReport a.actual.candidate.decl).verdict = true := by
      simpa [check,seen] using yes
    obtain ⟨tree,verdict,output⟩ := Check408.matchesNoWrites_exact408.mp result
    refine ⟨a,rfl,?_⟩
    cases r
    simp only at tree verdict output
    subst_vars
    rfl

theorem check_has_exact_original_report416 (p : Problem) (r : Result) (w : Witness)
    (yes : check p r w = true) : ClassifiedAs p.state p.root r := by
  cases w with
  | previous old => exact existing_exact_report_lifts416 (ClosedResidual415.check_sound p r old yes).1
  | plainMerged fresh =>
    obtain ⟨v,_,report⟩ := checked_plain_merge_reflects_original416 p r fresh yes
    exact report ▸ exact_plain_merge_has_selected_report416 v
  | unsupported => simp [check] at yes

theorem check_sound (p : Problem) (r : Result) (w : Witness) (yes : check p r w = true) :
    ClassifiedAs p.state p.root r ∧ ∀ m : I72.Model, Fits p.state m → ReportEvidence p.state m p.root r := by
  have ok := check_has_exact_original_report416 p r w yes
  refine ⟨ok,?_⟩
  obtain ⟨e,t,summary,out⟩ := ok
  exact fun m fit => ⟨e,t,summary,out,plain_R8_trace_model_meaning416 t m fit⟩

end Yulang.GeneralDeclarativeI65.I72.PlainMerged416
