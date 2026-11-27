import Yulang.GeneralDeclarativeI65I74WhereOutputBatch452

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.WhereSites450.OriginalCohorts451.GroupedEntry453
open Yulang.GeneralDeclarativeI65
open RetainedFull445
open OutputPhase452
open InternalK2452
open LiteralAndInternal452

abbrev OriginView := Nat × Nat × List Nat × Nat × Nat × Bool
abbrev CohortView := List OriginView

/-- The exact scoped grouped K2 diagnostic fragment. A position is
always in a complete ordered list; there is no primary position. -/
structure GroupedReport where
  parentOccurrence : List Nat
  parentImpl : Nat
  origins : List CohortView

def originGroups {p : FullProblem} (x : ScopedLiteralReport p) : List CohortView :=
  x.internal.groups.map fun g => g.marks.map OriginalMark.literal

def exactReport {p : FullProblem} (x : ScopedLiteralReport p) : GroupedReport :=
  ⟨p.root.occurrence,x.actual.parent.decl.id,originGroups x⟩

def SameReport (a b : GroupedReport) : Prop :=
  a.parentOccurrence = b.parentOccurrence ∧ a.parentImpl = b.parentImpl ∧ a.origins.Perm b.origins

def matchesReport (a b : GroupedReport) : Bool :=
  (a.parentOccurrence == b.parentOccurrence) &&
    (a.parentImpl == b.parentImpl) && a.origins.isPerm b.origins

theorem matches_reflects_exact_origins453 (a b : GroupedReport) :
    matchesReport a b = true ↔ SameReport a b := by
  simp [matchesReport,SameReport,Bool.and_eq_true,List.isPerm_iff,and_assoc]

/-- Sufficient complete identity scope: no two raw classes share a
role. Positive aliases are real same-input evidence; across roles,
the established same-role condition precludes merging. A raw failure
at two same-role sites is *not* a proof that they cannot merge. -/
def WholeRoster {p : FullProblem} (x : ScopedLiteralReport p) : Prop :=
  ∀ a ∈ x.actual.diagnostics.cohorts.labelled,
    ∀ b ∈ x.actual.diagnostics.cohorts.labelled, a.1.1 = b.1.1 → a.2 = b.2

def wholeRosterCheck {p : FullProblem} (x : ScopedLiteralReport p) : Bool :=
  let sites := x.actual.diagnostics.cohorts.labelled
  sites.all fun a => sites.all fun b => !(a.1.1 == b.1.1) || a.2 == b.2

theorem whole_roster_check_reflects_sufficient_scope453 {p : FullProblem}
    (x : ScopedLiteralReport p) : wholeRosterCheck x = true ↔ WholeRoster x := by
  simp only [wholeRosterCheck,WholeRoster,List.all_eq_true,Bool.or_eq_true,
    Bool.not_eq_true',beq_iff_eq,beq_eq_false_iff_ne]
  constructor
  · intro h a first b last same
    exact (h a first b last).resolve_left (fun h => h same)
  · intro h a first b last
    by_cases same : a.1.1 = b.1.1
    · exact .inr (h a first b last same)
    · exact .inl same

/-- Both directions at every pair of genuine constructed source sites.
This is conditional on the whole-roster certificate, not a converse
from general semantic equality to raw Alias. -/
theorem certified_class_iff_same_inputs_at_both_actual_sites453 {p : FullProblem}
    (packet : ScopedLiteralReport p) (all : WholeRoster packet)
    {i j : Nat} (x : SourcePointAt packet.actual.parent i) (y : SourcePointAt packet.actual.parent j)
    {l r : Nat}
    (left : packet.actual.diagnostics.cohorts.labelled[i]? = some (x.actual.tag,l))
    (right : packet.actual.diagnostics.cohorts.labelled[j]? = some (y.actual.tag,r)) :
    l = r ↔ GeneralNominalDemandMerging.SameInputs (allAssignments p.state) x.site y.site := by
  constructor
  · intro same
    subst r
    exact (indexed_cohort_label_proves_same_input_from_actual_source451
      packet.actual.diagnostics.cohorts x y l left right).1
  · intro same
    exact all _ (List.mem_of_getElem? left) _ (List.mem_of_getElem? right) same.1

/-- An independent exact scoped report derives from an actual
positional source derivation and real raw cohorts, not check success. -/
def ExactGrouped (p : FullProblem) (r : GroupedReport) : Prop :=
  ∃ x : ScopedLiteralReport p, WholeRoster x ∧ SameReport r (exactReport x)

def GroupedEvidence (p : FullProblem) (m : I72.Model) (r : GroupedReport) : Prop :=
  ∃ x : ScopedLiteralReport p, WholeRoster x ∧ SameReport r (exactReport x) ∧
    WhereSites450.ReportEvidence p.state.base m p.root x.localK2.report

theorem scoped_grouped_sound_at_every_fit453 {p : FullProblem} {r : GroupedReport}
    (h : ExactGrouped p r) (m : I72.Model) (fit : FitsFull p.state m) :
    GroupedEvidence p m r := by
  obtain ⟨x,whole,same⟩ := h
  exact ⟨x,whole,same,(any_literal_replay_preserves_original_scoped_report_meaning452 p x).2 m fit⟩

def checkGrouped453 (p : FullProblem) (r : GroupedReport) (w : ScopedLiteralInput) : Bool :=
  ((readScopedLiteralReport p w).map fun x => wholeRosterCheck x && matchesReport r (exactReport x)).getD false

theorem exact_scoped_grouped_report_iff_finite_wire453 (p : FullProblem) (r : GroupedReport) :
    (∃ w, checkGrouped453 p r w = true) ↔ ExactGrouped p r := by
  constructor
  · rintro ⟨w,ok⟩
    cases h : readScopedLiteralReport p w with
    | none => simp [checkGrouped453,h] at ok
    | some x =>
      have output : wholeRosterCheck x = true ∧ matchesReport r (exactReport x) = true := by
        simpa [checkGrouped453,h] using ok
      exact ⟨x,(whole_roster_check_reflects_sufficient_scope453 x).mp output.1,
        (matches_reflects_exact_origins453 _ _).mp output.2⟩
  · rintro ⟨x,whole,same⟩
    obtain ⟨w,read⟩ := source_cohorts_and_literal_report_replay_together452 p x
    exact ⟨w,by simp [checkGrouped453,read,(whole_roster_check_reflects_sufficient_scope453 x).mpr whole,
      (matches_reflects_exact_origins453 _ _).mpr same]⟩

inductive Report where
  | previous (result : Checker408.Result)
  | grouped (result : GroupedReport)

inductive Witness where
  | previous (data : WhereSites450.Witness)
  | grouped (data : ScopedLiteralInput)

def check_full453 (p : FullProblem) : Report → Witness → Bool
  | .previous r, .previous w => NoSiblingMerge.check_full450 p r w
  | .grouped r, .grouped w => checkGrouped453 p r w
  | _, _ => false

theorem all_previous_witness_Bools_unchanged453 (p : FullProblem) (r : Checker408.Result)
    (w : WhereSites450.Witness) :
    check_full453 p (.previous r) (.previous w) = NoSiblingMerge.check_full450 p r w := rfl

def ClassifiedAs (p : FullProblem) : Report → Prop
  | .previous r => NoSiblingMerge.ClassifiedAs p r
  | .grouped r => ExactGrouped p r

def ReportEvidence (p : FullProblem) (m : I72.Model) : Report → Prop
  | .previous r => NoSiblingMerge.ReportEvidence p m r
  | .grouped r => GroupedEvidence p m r

theorem check_full_sound453 (p : FullProblem) (r : Report) (w : Witness)
    (ok : check_full453 p r w = true) :
    ClassifiedAs p r ∧ ∀ m, FitsFull p.state m → ReportEvidence p m r := by
  cases r with
  | previous r =>
    cases w with
    | previous w => exact NoSiblingMerge.check_full_sound450 p r w ok
    | grouped w => cases ok
  | grouped r =>
    cases w with
    | previous w => cases ok
    | grouped w =>
      have chosen := (exact_scoped_grouped_report_iff_finite_wire453 p r).mp ⟨w,ok⟩
      exact ⟨chosen,scoped_grouped_sound_at_every_fit453 chosen⟩

theorem scoped_independent_exact_grouped_has_cumulative_witness453
    (p : FullProblem) (r : GroupedReport) (h : ExactGrouped p r) :
    ∃ w, check_full453 p (.grouped r) (.grouped w) = true :=
  (exact_scoped_grouped_report_iff_finite_wire453 p r).mpr h

end Yulang.GeneralDeclarativeI65.I72.WhereSites450.OriginalCohorts451.GroupedEntry453
