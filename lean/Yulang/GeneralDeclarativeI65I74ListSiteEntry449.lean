import Yulang.GeneralDeclarativeI65I74ListSiteRead449

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.ListSites449
open Yulang.GeneralDeclarativeI65
open Checker408 (Result)
open GeneralDeclarations (Declaration)
open RetainedFull445
open List410 (VerifiedList)
open Opaque448.Whole (ClassifiedAs448 ReportEvidence448)

structure LocalChoice (p : FullProblem) where
  decl : Declaration
  source : VerifiedList p.old decl

def LocalChoice.report {p : FullProblem} (a : LocalChoice p) : Result :=
  Check408.nullaryReport a.decl

theorem list_exact_report_is_in_existing_R13 {p : FullProblem} (a : LocalChoice p) :
    RepeatedCenters421.ClassifiedAs p.state.base p.root a.report := by
  let c410 := List410.list_choice_has_exact_R2_report410 a.source
  let c411 := WhereCycle411.existing_exact_report_lifts411 c410
  let c412 := RecordK2412.existing_exact_report_lifts412 c411
  let c413 := MixedRecord413.existing_exact_report_lifts413 c412
  let c414 := OpenTail414.existing_exact_report_lifts414 c413
  let c415 := ClosedResidual415.existing_exact_report_lifts415 c414
  let c416 := PlainMerged416.existing_exact_report_lifts416 c415
  let c417 := X6Ambiguous417.existing_exact_report_lifts417 c416
  let c418 := RigidRival418.existing_exact_report_lifts418 c417
  let c419 := ExplicitPick419.existing_exact_report_lifts419 c418
  let c420 := RoleDefault420.existing_exact_report_lifts420 c419
  let c421 := RepeatedCenters421.existing_exact_report_lifts421 c420
  exact c421

theorem independent_list_report_sound449 {p : FullProblem} (a : LocalChoice p) :
    ClassifiedAs448 p a.report ∧
      ∀ m, FitsFull p.state m → ReportEvidence448 p m a.report := by
  have chosen := list_exact_report_is_in_existing_R13 a
  refine ⟨.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl chosen))))))))),?_⟩
  intro m fit
  obtain ⟨e,t,summary,writes⟩ := chosen
  have evidence : RepeatedCenters421.ReportEvidence p.state.base m p.root a.report :=
    ⟨e,t,summary,writes,RepeatedCenters421.repeated_R13_trace_model_meaning421 t m fit.1⟩
  exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl evidence)))))))))

inductive Witness where
  | previous (old : Opaque448.Whole.Witness)
  | inspectedList (new : Wire)

/-- One cumulative checker. The only new branch runs the exact original
site read, checks its per-position cut table, and compares every field
of the original selected report; old witnesses run unchanged. -/
def check_full449 (p : FullProblem) (r : Result) : Witness → Bool
  | .previous old => Opaque448.Whole.check_full448 p r old
  | .inspectedList w =>
    match scope : visible p.state.base.core p.root with
    | [d] => (readListSites p.old d scope w).isSome &&
        Check408.matchesNoWrites r (.selected d.id []) (.selected (.node d.id []))
    | _ => false

theorem previous_witness_Bool_unchanged449 (p : FullProblem) (r : Result)
    (old : Opaque448.Whole.Witness) :
    check_full449 p r (.previous old) = Opaque448.Whole.check_full448 p r old := rfl

private theorem exact_report (d : Declaration) (r : Result) :
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

theorem accepted_list_report_reads_exact_declaration449 {p : FullProblem} {r : Result} {w : Wire}
    (yes : check_full449 p r (.inspectedList w) = true) :
    ∃ a : LocalChoice p, r = a.report ∧ readListSites p.old a.decl a.source.known.only w = some a.source := by
  simp only [check_full449] at yes
  split at yes
  · rename_i d scope
    obtain ⟨checkRead,report⟩ := Bool.and_eq_true_iff.mp yes
    cases got : readListSites p.old d scope w with
    | none => simp [got] at checkRead
    | some a => exact ⟨⟨d,a⟩,(exact_report d r).mp report,got⟩
  · simp at yes

theorem independent_list_reifies_its_exact_report449 {p : FullProblem} (a : LocalChoice p) :
    ∃ w : Wire, check_full449 p a.report (.inspectedList w) = true := by
  obtain ⟨w,h⟩ := independent_list_has_exact_per_site_wire449 a.source
  refine ⟨w,?_⟩
  simp only [check_full449]
  split
  · rename_i d scope
    have same := List.singleton_inj.mp (scope.symm.trans a.source.known.only)
    subst d
    rw [h]
    exact Bool.and_eq_true_iff.mpr ⟨rfl,(exact_report _ _).mpr rfl⟩
  · rename_i wrong
    exact (wrong _ a.source.known.only).elim

theorem list_wire_iff_actual_local_selection449 (p : FullProblem) (r : Result) :
    (∃ w : Wire, check_full449 p r (.inspectedList w) = true) ↔
      ∃ a : LocalChoice p, r = a.report := by
  constructor
  · rintro ⟨w,yes⟩
    obtain ⟨a,report,_⟩ := accepted_list_report_reads_exact_declaration449 yes
    exact ⟨a,report⟩
  · rintro ⟨a,rfl⟩
    exact independent_list_reifies_its_exact_report449 a

theorem original_root_cycle_declines_all_list_wires449 {p : FullProblem}
    (cycle : RootCycle p.state.base p.root) (r : Result) (w : Wire) :
    check_full449 p r (.inspectedList w) = false := by
  cases h : check_full449 p r (.inspectedList w) with
  | false => rfl
  | true =>
    obtain ⟨a,_,_⟩ := accepted_list_report_reads_exact_declaration449 h
    exact (a.source.rawSafe cycle).elim

theorem check_full_sound449 (p : FullProblem) (r : Result) (w : Witness)
    (yes : check_full449 p r w = true) :
    ClassifiedAs448 p r ∧ ∀ m, FitsFull p.state m → ReportEvidence448 p m r := by
  cases w with
  | previous old => exact Opaque448.Whole.check_full_sound448 p r old yes
  | inspectedList w =>
    obtain ⟨a,same,_⟩ := accepted_list_report_reads_exact_declaration449 yes
    exact same.symm ▸ independent_list_report_sound449 a

end Yulang.GeneralDeclarativeI65.I72.ListSites449
