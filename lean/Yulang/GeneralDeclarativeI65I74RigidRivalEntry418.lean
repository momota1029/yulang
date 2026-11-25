import Yulang.GeneralDeclarativeI65I74RigidRivalReport418
import Yulang.GeneralDeclarativeI65I74RigidRivalReplay418

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RigidRival418
open GeneralDeclarativeI65
open CommonRoleOutermostResolver (Summarizes)
open Checker408 (Problem Result)

theorem exact_plain_merge_has_selected_report418 {p : Problem} (a : Winner p.state p.root) :
    ClassifiedAs p.state p.root (Check408.nullaryReport a.winner.candidate.decl) := by
  let event := a.winner.event
  let noneKids : WhereForest R10 p.state event.kids [] :=
    (exact_winner_has_no_where418 a).symm ▸ (.nil : WhereForest R10 p.state [] [])
  let original : SourceTrace R10 p.state p.root
      (.selected a.winner.candidate.decl.id []) (some event) :=
    .selected event (X6Ambiguous417.root_safe417 a.inspections) (.inr ⟨rfl,⟨.actual a⟩⟩) .nil noneKids
  have noWrites : Check408.encodedEventWrites event = [] :=
    List.length_eq_zero_iff.mp (by simp [Check408.encodedEventWrites,a.rows.noOutputs])
  have noneWrites : ∀ qs (h : qs = []),
      forestWrites (h.symm ▸ (.nil : WhereForest R10 p.state [] [])) = [] := by
    intro qs h
    cases h
    rfl
  have same : writes original = [] := by
    change Check408.encodedEventWrites event ++ forestWrites noneKids = []
    have none := noneWrites _ (exact_winner_has_no_where418 a)
    rw [noWrites,none]
    rfl
  exact ⟨some event,original,.selected .nil (.selected rfl),same.symm⟩

inductive Witness where
  | previous (old : X6Ambiguous417.Witness)
  | rigidRival (w : RivalWire)
  | unsupported

def check (p : Problem) (r : Result) : Witness → Bool
  | .previous old => X6Ambiguous417.check p r old
  | .rigidRival w =>
    match replayWinner418 p w with
    | none => false
    | some a =>
      let verdict := Check408.nullaryReport a.winner.candidate.decl
      Check408.matchesNoWrites r verdict.tree verdict.verdict
  | .unsupported => false

theorem previous_entry_unchanged418 (p : Problem) (r : Result) (w : X6Ambiguous417.Witness) :
    check p r (.previous w) = X6Ambiguous417.check p r w := rfl

theorem checked_plain_merge_reflects_original418 (p : Problem) (r : Result) (w : RivalWire)
    (yes : check p r (.rigidRival w) = true) :
    ∃ v, replayWinner418 p w = some v ∧ r = Check408.nullaryReport v.winner.candidate.decl := by
  cases seen : replayWinner418 p w with
  | none => simp [check,seen] at yes
  | some a =>
    have result : Check408.matchesNoWrites r (Check408.nullaryReport a.winner.candidate.decl).tree
        (Check408.nullaryReport a.winner.candidate.decl).verdict = true := by
      simpa [check,seen] using yes
    obtain ⟨tree,verdict,output⟩ := Check408.matchesNoWrites_exact408.mp result
    refine ⟨a,rfl,?_⟩
    cases r
    simp only at tree verdict output
    subst_vars
    rfl

theorem check_has_exact_original_report418 (p : Problem) (r : Result) (w : Witness)
    (yes : check p r w = true) : ClassifiedAs p.state p.root r := by
  cases w with
  | previous old => exact existing_exact_report_lifts418 (X6Ambiguous417.check_sound p r old yes).1
  | rigidRival fresh =>
    obtain ⟨v,_,report⟩ := checked_plain_merge_reflects_original418 p r fresh yes
    exact report ▸ exact_plain_merge_has_selected_report418 v
  | unsupported => simp [check] at yes

theorem check_sound (p : Problem) (r : Result) (w : Witness) (yes : check p r w = true) :
    ClassifiedAs p.state p.root r ∧ ∀ m : I72.Model, Fits p.state m → ReportEvidence p.state m p.root r := by
  have ok := check_has_exact_original_report418 p r w yes
  refine ⟨ok,?_⟩
  obtain ⟨e,t,summary,out⟩ := ok
  exact fun m fit => ⟨e,t,summary,out,rigid_R10_trace_model_meaning418 t m fit⟩

end Yulang.GeneralDeclarativeI65.I72.RigidRival418
