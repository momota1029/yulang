import Yulang.GeneralDeclarativeI65I74OpaqueRead448

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.Opaque448
open Yulang.GeneralDeclarativeI65
open Checker408 (Problem Result)
open GeneralDeclarations (Declaration)
open RetainedFull445
open Named409 (VerifiedName)
open RetainedSplit446.SelectedReplay447 (Witness447 check_full447)

structure ResolvedChoice (p : FullProblem) where
  decl : Declaration
  read : VerifiedName p.old decl

def ResolvedChoice.report {p : FullProblem} (a : ResolvedChoice p) : Result :=
  Check408.nullaryReport a.decl

/-- Preserve the exact report while transporting the independently
supported R1 leaf through the prior accepted inclusions; no new
declarative meaning of the head is introduced. -/
theorem opaque_report_in_existing_R13 {p : FullProblem} (a : ResolvedChoice p) :
    RepeatedCenters421.ClassifiedAs p.state.base p.root a.report := by
  let c409 := Named409.named_choice_has_exact_R1_report409 a.read
  let c410 := List410.existing_exact_report_lifts410 c409
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

theorem independent_resolved_choice_sound448 {p : FullProblem} (a : ResolvedChoice p) :
    ClassifiedAsFull p.state p.root a.report ∧
      ∀ m, FitsFull p.state m → ReportEvidenceFull p.state m p.root a.report := by
  have chosen := opaque_report_in_existing_R13 a
  refine ⟨.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl chosen)))))))),?_⟩
  intro m fit
  obtain ⟨e,t,summary,writes⟩ := chosen
  have evidence : RepeatedCenters421.ReportEvidence p.state.base m p.root a.report :=
    ⟨e,t,summary,writes,RepeatedCenters421.repeated_R13_trace_model_meaning421 t m fit.1⟩
  exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl evidence))))))))

inductive Witness448 where
  | previous (w : Witness447)
  | opaqueName (w : NamedWire)

def check_full448 (p : FullProblem) (r : Result) : Witness448 → Bool
  | .previous old => check_full447 p r old
  | .opaqueName w =>
    match scope : visible p.state.base.core p.root with
    | [d] => (readOpaque p.old d scope w).isSome &&
        Check408.matchesNoWrites r (.selected d.id []) (.selected (.node d.id []))
    | _ => false

theorem all_previous_Bool_unchanged448 (p : FullProblem) (r : Result) (w : Witness447) :
    check_full448 p r (.previous w) = check_full447 p r w := rfl

private theorem matches_named_report_exact (d : Declaration) (r : Result) :
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

theorem accepted_opaque_has_exact_choice448 {p : FullProblem} {r : Result} {w : NamedWire}
    (ok : check_full448 p r (.opaqueName w) = true) :
    ∃ a : ResolvedChoice p, r = a.report := by
  simp only [check_full448] at ok
  split at ok
  · rename_i d scope
    obtain ⟨replay,report⟩ := Bool.and_eq_true_iff.mp ok
    cases got : readOpaque p.old d scope w with
    | none => simp [got] at replay
    | some a => exact ⟨⟨d,a⟩,(matches_named_report_exact d r).mp report⟩
  · simp at ok

theorem independent_choice_has_exact_check448 {p : FullProblem} (a : ResolvedChoice p) :
    ∃ w : NamedWire, check_full448 p a.report (.opaqueName w) = true := by
  obtain ⟨w,replayed⟩ := independent_opaque_has_wire448 a.read
  refine ⟨w,?_⟩
  simp only [check_full448]
  split
  · rename_i d scope
    have declEq : d = a.decl := List.singleton_inj.mp (scope.symm.trans a.read.known.only)
    subst d
    rw [replayed]
    exact Bool.and_eq_true_iff.mpr ⟨rfl,(matches_named_report_exact _ _).mpr rfl⟩
  · rename_i notSingle
    exact (notSingle _ a.read.known.only).elim

theorem check_full_sound448 (p : FullProblem) (r : Result) (w : Witness448)
    (yes : check_full448 p r w = true) :
    ClassifiedAsFull p.state p.root r ∧
      ∀ m : I72.Model, FitsFull p.state m → ReportEvidenceFull p.state m p.root r := by
  cases w with
  | previous w => exact RetainedSplit446.SelectedReplay447.check_full_sound447 p r w yes
  | opaqueName w =>
    obtain ⟨a,report⟩ := accepted_opaque_has_exact_choice448 yes
    exact report.symm ▸ independent_resolved_choice_sound448 a

theorem opaque_report_iff_independent_choice448 (p : FullProblem) (r : Result) :
    (∃ w : NamedWire, check_full448 p r (.opaqueName w) = true) ↔
      ∃ a : ResolvedChoice p, r = a.report :=
  ⟨fun ⟨_,yes⟩ => accepted_opaque_has_exact_choice448 yes,
    fun ⟨a,report⟩ => report.symm ▸ independent_choice_has_exact_check448 a⟩

theorem local_opaque_declines_nonsingleton448 {p : FullProblem} {r : Result}
    (notSingleton : (visible p.state.base.core p.root).length ≠ 1) (w : NamedWire) :
    check_full448 p r (.opaqueName w) = false := by
  cases h : check_full448 p r (.opaqueName w) with
  | false => rfl
  | true =>
    obtain ⟨a,_⟩ := accepted_opaque_has_exact_choice448 h
    have one : visible p.state.base.core p.root = [a.decl] := a.read.known.only
    exact (notSingleton (by rw [one]; rfl)).elim

end Yulang.GeneralDeclarativeI65.I72.Opaque448
