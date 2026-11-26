import Yulang.GeneralDeclarativeI65I74OpaqueWholeRule448

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.Opaque448.Whole
open Yulang.GeneralDeclarativeI65
open Checker408 (Result)
open RetainedFull445
open Roster
open CommonRoleOutermostResolver (Summarizes)

def ClassifiedAs448 (p : FullProblem) (r : Result) : Prop :=
  ClassifiedAsFull p.state p.root r ∨ ∃ a : WholeChoice p.old, r = a.report

def ReportEvidence448 (p : FullProblem) (m : I72.Model) (r : Result) : Prop :=
  ReportEvidenceFull p.state m p.root r ∨
    ∃ a : WholeChoice p.old, r = a.report ∧
      ∃ e : Event p.state.base p.root,
        Nonempty (SourceTrace wholeRule p.state.base p.root r.tree (some e)) ∧
        Summarizes r.tree r.verdict ∧
        r.writes = Check408.encodedEventWrites e ∧
        DictionaryEvidence p.state.base m p.root (.node a.picked.id [])

inductive Witness where
  | previous (w : Opaque448.Witness448)
  | wholeBare (wire : Opaque448.NamedWire)

/-- One cumulative entry. Earlier witnesses (including C447, and the
original scoped C448 branch) are delegated without any new guard. -/
def check_full448 (p : FullProblem) (r : Result) : Witness → Bool
  | .previous old => Opaque448.check_full448 p r old
  | .wholeBare w =>
    match readWholeChoice p.old w with
    | none => false
    | some derived =>
      Check408.matchesNoWrites r (.selected derived.picked.id []) (.selected (.node derived.picked.id []))

theorem all_earlier_witnesses_unchanged448 (p : FullProblem) (r : Result)
    (w : Opaque448.Witness448) :
    check_full448 p r (.previous w) = Opaque448.check_full448 p r w := rfl

theorem all_C447_witnesses_unchanged448 (p : FullProblem) (r : Result)
    (w : RetainedSplit446.SelectedReplay447.Witness447) :
    check_full448 p r (.previous (.previous w)) =
      RetainedSplit446.SelectedReplay447.check_full447 p r w := rfl

private theorem exact_report_test (a : WholeChoice p) (r : Result) :
    Check408.matchesNoWrites r (.selected a.picked.id []) (.selected (.node a.picked.id [])) = true ↔
    r = a.report := by
  constructor
  · intro h
    obtain ⟨tree,verdict,writes⟩ := Check408.matchesNoWrites_exact408.mp h
    cases r
    simp only at tree verdict writes
    subst_vars
    rfl
  · intro h
    subst r
    exact Check408.matchesNoWrites_exact408.mpr ⟨rfl,rfl,rfl⟩

theorem accepted_whole_wire_is_exact_choice448 {p : FullProblem} {r : Result} {w : NamedWire}
    (yes : check_full448 p r (.wholeBare w) = true) :
    ∃ a : WholeChoice p.old, readWholeChoice p.old w = some a ∧ r = a.report := by
  simp only [check_full448] at yes
  cases h : readWholeChoice p.old w with
  | none => simp [h] at yes
  | some a =>
    rw [h] at yes
    exact ⟨a,rfl,(exact_report_test a r).mp yes⟩

theorem independent_whole_choice_reifies_exact_report448 (p : FullProblem)
    (a : WholeChoice p.old) :
    ∃ w : NamedWire, check_full448 p a.report (.wholeBare w) = true := by
  obtain ⟨w,read⟩ := whole_choice_has_exact_replay448 a
  exact ⟨w,by simp only [check_full448,read]; exact (exact_report_test a _).mpr rfl⟩

theorem whole_wire_iff_exact_independent_report448 (p : FullProblem) (r : Result) :
    (∃ w : NamedWire, check_full448 p r (.wholeBare w) = true) ↔
      ∃ a : WholeChoice p.old, r = a.report := by
  constructor
  · rintro ⟨w,yes⟩
    obtain ⟨a,_,report⟩ := accepted_whole_wire_is_exact_choice448 yes
    exact ⟨a,report⟩
  · rintro ⟨a,rfl⟩
    exact independent_whole_choice_reifies_exact_report448 p a

theorem check_full_sound448 (p : FullProblem) (r : Result) (w : Witness)
    (yes : check_full448 p r w = true) :
    ClassifiedAs448 p r ∧ ∀ m, FitsFull p.state m → ReportEvidence448 p m r := by
  cases w with
  | previous old =>
    have valid := Opaque448.check_full_sound448 p r old yes
    exact ⟨.inl valid.1,fun m fit => .inl (valid.2 m fit)⟩
  | wholeBare wire =>
    obtain ⟨a,_,report⟩ := accepted_whole_wire_is_exact_choice448 yes
    obtain ⟨e,tr,writes,model⟩ := whole_choice_assembly448 a
    refine ⟨.inr ⟨a,report⟩,fun m fit => .inr ⟨a,report,e,?_,?_,?_,model m fit.1⟩⟩
    · exact report.symm ▸ tr
    · rw [report]
      exact .selected .nil (.selected rfl)
    · exact report.symm ▸ writes

end Yulang.GeneralDeclarativeI65.I72.Opaque448.Whole
