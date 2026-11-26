import Yulang.GeneralDeclarativeI65I74ListFrameRule449

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.ListSites449.Frame
open Yulang.GeneralDeclarativeI65
open Checker408 (Result)
open RetainedFull445
open CommonRoleOutermostResolver (Summarizes)
open GeneralDeclarations (Declaration)
open GeneralDeclarativeWitnessDeclaredState357 (point)
open GeneralDeclarativeWhere319 (Capture)

def ClassifiedAs449 (p : FullProblem) (r : Result) : Prop :=
  Opaque448.Whole.ClassifiedAs448 p r ∨ ∃ a : FramedSelection p.old, r = a.report

def ReportEvidence449 (p : FullProblem) (m : I72.Model) (r : Result) : Prop :=
  Opaque448.Whole.ReportEvidence448 p m r ∨
    ∃ a : FramedSelection p.old, r = a.report ∧
      ∃ e : Event p.state.base p.root,
        Nonempty (SourceTrace listFrameRule p.state.base p.root r.tree (some e)) ∧
        Summarizes r.tree r.verdict ∧
        r.writes = Check408.encodedEventWrites e ∧
        (∀ b u, (b,u) ∈ a.chosen.roster.bindings → e.frame.input b = point u) ∧
        I72.DictionaryEvidence p.state.base m p.root (.node a.decl.id [])

inductive Witness where
  | previous (old : ListSites449.Witness)
  | inspectedFrame (w : FrameWire)

/-- Cumulative entry with one local G02 generalization. The new wire
names only original origin indexes, and separate cut data in exact
written position order. No sites, options, report, or models are trusted. -/
def check_full449 (p : FullProblem) (r : Result) : Witness → Bool
  | .previous old => ListSites449.check_full449 p r old
  | .inspectedFrame w =>
    match scope : visible p.state.base.core p.root with
    | [d] => (readListFrameChoice p.old d scope w).isSome &&
        Check408.matchesNoWrites r (.selected d.id []) (.selected (.node d.id []))
    | _ => false

theorem all_previous_frame_witnesses_unchanged449 (p : FullProblem) (r : Result) (w : ListSites449.Witness) :
    check_full449 p r (.previous w) = ListSites449.check_full449 p r w := rfl

theorem all_C448_witnesses_unchanged449 (p : FullProblem) (r : Result) (w : Opaque448.Whole.Witness) :
    check_full449 p r (.previous (.previous w)) = Opaque448.Whole.check_full448 p r w := rfl

private theorem frame_comparison_is_exact (d : Declaration) (r : Result) :
    Check408.matchesNoWrites r (.selected d.id []) (.selected (.node d.id [])) = true ↔
    r = Check408.nullaryReport d := by
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

theorem actual_checked_frame_reads_exact_source449 {p : FullProblem} {r : Result} {w : FrameWire}
    (yes : check_full449 p r (.inspectedFrame w) = true) :
    ∃ a : FramedSelection p.old, r = a.report ∧
      readListFrameChoice p.old a.decl a.chosen.only w = some a.chosen := by
  simp only [check_full449] at yes
  split at yes
  · rename_i d scope
    obtain ⟨replay,report⟩ := Bool.and_eq_true_iff.mp yes
    cases hit : readListFrameChoice p.old d scope w with
    | none => simp [hit] at replay
    | some a => exact ⟨⟨d,a⟩,(frame_comparison_is_exact _ _).mp report,hit⟩
  · simp at yes

theorem independent_selected_frame_reifies_exact_report449 {p : FullProblem} (a : FramedSelection p.old) :
    ∃ w, check_full449 p a.report (.inspectedFrame w) = true := by
  obtain ⟨wire,replay⟩ := independent_list_frame_replays_exactly449 a.chosen
  refine ⟨wire,?_⟩
  simp only [check_full449]
  split
  · rename_i d roster
    have same : d = a.decl := List.singleton_inj.mp (roster.symm.trans a.chosen.only)
    subst d
    rw [replay]
    exact Bool.and_eq_true_iff.mpr ⟨rfl,(frame_comparison_is_exact _ _).mpr rfl⟩
  · rename_i missing
    exact (missing _ a.chosen.only).elim

theorem exact_frame_wire_iff_independent_report449 (p : FullProblem) (r : Result) :
    (∃ wire : FrameWire, check_full449 p r (.inspectedFrame wire) = true) ↔
    ∃ a : FramedSelection p.old, r = a.report := by
  constructor
  · rintro ⟨wire,valid⟩
    obtain ⟨a,report,_⟩ := actual_checked_frame_reads_exact_source449 valid
    exact ⟨a,report⟩
  · rintro ⟨a,rfl⟩
    exact independent_selected_frame_reifies_exact_report449 a

theorem any_actual_inspected_root_cycle_declines_frame449 {p : FullProblem}
    (cycle : RootCycle p.state.base p.root) (r : Result) (w : FrameWire) :
    check_full449 p r (.inspectedFrame w) = false := by
  cases h : check_full449 p r (.inspectedFrame w) with
  | false => rfl
  | true =>
    obtain ⟨a,_,_⟩ := actual_checked_frame_reads_exact_source449 h
    exact (a.chosen.safe cycle).elim

theorem check_full_sound449 (p : FullProblem) (r : Result) (w : Witness)
    (ok : check_full449 p r w = true) :
    ClassifiedAs449 p r ∧ ∀ m, FitsFull p.state m → ReportEvidence449 p m r := by
  cases w with
  | previous old =>
    have checked := ListSites449.check_full_sound449 p r old ok
    exact ⟨.inl checked.1,fun m fit => .inl (checked.2 m fit)⟩
  | inspectedFrame wire =>
    obtain ⟨a,report,_⟩ := actual_checked_frame_reads_exact_source449 ok
    obtain ⟨e,tr,writes,caps,meaning⟩ := exact_framed_selection_assembly449 a
    refine ⟨.inr ⟨a,report⟩,fun m fit => .inr ⟨a,report,e,?_,?_,?_,caps,meaning m fit.1⟩⟩
    · exact report.symm ▸ tr
    · rw [report]
      exact .selected .nil (.selected rfl)
    · exact report.symm ▸ writes

end Yulang.GeneralDeclarativeI65.I72.ListSites449.Frame
