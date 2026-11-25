import Yulang.GeneralDeclarativeI65I74ClosedResidualReport415
import Yulang.GeneralDeclarativeI65I74ClosedResidualReplay415

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.ClosedResidual415
open GeneralDeclarativeI65
open CommonRoleOutermostResolver (Dictionary Tree Summarizes)
open Checker408 (Problem Result)

def exactReport (p c : GeneralDeclarations.Declaration) : Result :=
  ⟨.selected p.id [.selected c.id []],.selected (.node p.id [.node c.id []]),[]⟩

private theorem noEventWrites {s q} (e : Event s q) (empty : q.demand.outputs = []) :
    Check408.encodedEventWrites e = [] :=
  List.length_eq_zero_iff.mp (by simp [Check408.encodedEventWrites,empty])

theorem complete_residual_has_exact_selected_report415 {p : Problem} (v : VerifiedClosed p) :
    ClassifiedAs p.state p.root (exactReport v.parent.candidate.decl v.child.candidate.decl) := by
  let a := v.rows
  let read := v.parent
  let child := v.child
  let parentEvent := read.event
  let childEvent := child.event
  let childKids : WhereForest R7 p.state childEvent.kids [] :=
    (residual_leaf_has_no_child415 child).symm ▸ (.nil : WhereForest R7 p.state [] [])
  let childTrace : SourceTrace R7 p.state (query415 p.root read.childRole a.residual)
      (.selected child.candidate.decl.id []) (some childEvent) :=
    .selected childEvent v.childSafe (.inr ⟨rfl,⟨.leaf a read child⟩⟩) .nil childKids
  let leaves : WhereForest R7 p.state [query415 p.root read.childRole a.residual]
      [.selected child.candidate.decl.id []] := .cons childTrace .nil
  let parentKids : WhereForest R7 p.state parentEvent.kids [.selected child.candidate.decl.id []] :=
    (parent_emits_actual_residual_child415 read).symm ▸ leaves
  let parentTrace : SourceTrace R7 p.state p.root
      (.selected read.candidate.decl.id [.selected child.candidate.decl.id []]) (some parentEvent) :=
    .selected parentEvent v.rootSafe (.inr ⟨rfl,⟨.parent a read⟩⟩) .nil parentKids
  have childSummarizes : Summarizes (.selected child.candidate.decl.id []) (.selected (.node child.candidate.decl.id [])) :=
    .selected .nil (.selected rfl)
  have ownSummary : Summarizes (.selected read.candidate.decl.id [.selected child.candidate.decl.id []])
      (.selected (.node read.candidate.decl.id [.node child.candidate.decl.id []])) :=
    .selected (.cons childSummarizes .nil) (.selected rfl)
  have childEmpty : ∀ qs (eq : qs = []), forestWrites (eq.symm ▸
      (.nil : WhereForest R7 p.state [] [])) = ([] : List Check408.Write) := by
    intro qs eq; cases eq; rfl
  have leafZero : writes childTrace = [] := by
    change Check408.encodedEventWrites childEvent ++ forestWrites childKids = []
    have e := childEmpty _ (residual_leaf_has_no_child415 child)
    rw [noEventWrites childEvent rfl,e]
    rfl
  have kidsZero : ∀ qs (eq : qs = [query415 p.root read.childRole a.residual]),
      forestWrites (eq.symm ▸ leaves) = [] := by
    intro qs eq
    cases eq
    change writes childTrace ++ [] = []
    rw [leafZero]; rfl
  have wholeZero : writes parentTrace = [] := by
    change Check408.encodedEventWrites parentEvent ++ forestWrites parentKids = []
    have e := kidsZero _ (parent_emits_actual_residual_child415 read)
    rw [noEventWrites parentEvent a.noOutputs,e]
    rfl
  exact ⟨some parentEvent,parentTrace,ownSummary,wholeZero.symm⟩

inductive Witness where
  | previous (w : OpenTail414.Witness)
  | closedRows (w : ClosedWire)
  | unsupported

def check (p : Problem) (r : Result) : Witness → Bool
  | .previous w => OpenTail414.check p r w
  | .closedRows w =>
    match replayClosed415 p w with
    | none => false
    | some v =>
      let desired := exactReport v.parent.candidate.decl v.child.candidate.decl
      Check408.matchesNoWrites r desired.tree desired.verdict
  | .unsupported => false

theorem previous_entry_unchanged415 (p : Problem) (r : Result) (old : OpenTail414.Witness) :
    check p r (.previous old) = OpenTail414.check p r old := rfl

theorem checked_closed_rows_reflect_original415 (p : Problem) (r : Result) (w : ClosedWire)
    (yes : check p r (.closedRows w) = true) :
    ∃ v, replayClosed415 p w = some v ∧ r = exactReport v.parent.candidate.decl v.child.candidate.decl := by
  cases replay : replayClosed415 p w with
  | none => simp [check,replay] at yes
  | some v =>
    have same : Check408.matchesNoWrites r
        (exactReport v.parent.candidate.decl v.child.candidate.decl).tree
        (exactReport v.parent.candidate.decl v.child.candidate.decl).verdict = true := by
      simpa [check,replay] using yes
    obtain ⟨tree,summary,out⟩ := Check408.matchesNoWrites_exact408.mp same
    refine ⟨v,rfl,?_⟩
    cases r
    simp only at tree summary out
    subst_vars
    rfl

theorem check_has_exact_original_report415 (p : Problem) (r : Result) (w : Witness)
    (yes : check p r w = true) : ClassifiedAs p.state p.root r := by
  cases w with
  | previous old => exact existing_exact_report_lifts415 (OpenTail414.check_sound p r old yes).1
  | unsupported => simp [check] at yes
  | closedRows fresh =>
    obtain ⟨v,_,report⟩ := checked_closed_rows_reflect_original415 p r fresh yes
    exact report ▸ complete_residual_has_exact_selected_report415 v

theorem check_sound (p : Problem) (r : Result) (w : Witness) (yes : check p r w = true) :
    ClassifiedAs p.state p.root r ∧ ∀ m : I72.Model, Fits p.state m → ReportEvidence p.state m p.root r := by
  have correct := check_has_exact_original_report415 p r w yes
  refine ⟨correct,?_⟩
  obtain ⟨e,t,summary,written⟩ := correct
  exact fun m fit => ⟨e,t,summary,written,closed_R7_trace_model_meaning415 t m fit⟩

end Yulang.GeneralDeclarativeI65.I72.ClosedResidual415
