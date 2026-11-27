import Yulang.GeneralDeclarativeI65I74WhereGroupedSource453

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.WhereSites450.OriginalCohorts451.SamePhase454
open Yulang.GeneralDeclarativeI65
open RetainedFull445
open InternalK2452
open OutputPhase452
open GroupedEntry453 (GroupedReport SameReport matchesReport matches_reflects_exact_origins453)

def exactReport {p : FullProblem} (x : InternalReport p) : GroupedReport :=
  ⟨p.root.occurrence,x.original.parent.decl.id,
    x.groups.map fun g => g.marks.map OriginalMark.literal⟩

/-- Exact source phase, not the result of re-aligning type names.
Only cyclic cohorts are reported; the exact raw profile still retains
all original safe sites. No premise that a safe sibling is selected. -/
def Exact (p : FullProblem) (r : GroupedReport) : Prop :=
  ∃ x : InternalReport p, x.groups ≠ [] ∧ SameReport r (exactReport x)

def check (p : FullProblem) (r : GroupedReport) (w : SourceDiagnosticWire) : Bool :=
  ((readInternalReport452 p w).map fun x =>
    !x.groups.isEmpty && matchesReport r (exactReport x)).getD false

theorem exact_same_phase_report_iff_finite_wire454 (p : FullProblem) (r : GroupedReport) :
    (∃ w, check p r w = true) ↔ Exact p r := by
  constructor
  · rintro ⟨w,ok⟩
    cases eq : readInternalReport452 p w with
    | none => simp [check,eq] at ok
    | some x =>
      have accept : x.groups ≠ [] ∧ matchesReport r (exactReport x) = true := by
        simpa [check,eq,Bool.and_eq_true,Bool.not_eq_true',List.isEmpty_eq_false_iff] using ok
      exact ⟨x,accept.1,(matches_reflects_exact_origins453 _ _).mp accept.2⟩
  · rintro ⟨x,nonempty,same⟩
    obtain ⟨w,read⟩ := independent_scoped_internal_report_has_finite_replay452 p x
    exact ⟨w,by simp [check,read,nonempty,List.isEmpty_eq_false_iff,
      (matches_reflects_exact_origins453 _ _).mpr same]⟩

/-- Model evidence of the genuine selected parent event before settling
siblings. No dictionary for a rejected child, nor any selectedness of
safe siblings, is asserted. The source has no associated outputs. -/
def ParentMeaning (p : FullProblem) (m : I72.Model) (x : InternalReport p) : Prop :=
  ∃ e : Event p.state.base p.root,
    e.frame.decl = x.original.parent.decl ∧ e.kids = x.original.parent.children ∧
      ¬ RootCycle p.state.base p.root ∧ LocalMeaning m e ∧ FixedTargets m e

theorem actual_parent_event_meaning_at_every_fit454 (p : FullProblem) (x : InternalReport p)
    (m : I72.Model) (fit : FitsFull p.state m) : ParentMeaning p m x := by
  let parent := x.original.parent
  obtain ⟨source⟩ := selected_head_original_origin395
    (actual_single_declaration_list_frame_is_settled450 parent.chosen)
  let e := parent.event source
  have localRule : parentWhereRule450.elected p.state.base p.root e [] :=
    ⟨rfl,.inl ⟨parent,source,rfl⟩⟩
  have localData := parent_where_local_evidence450 p.state.base p.root e [] localRule
  refine ⟨e,rfl,literal_parent_reconstructs_all_original_children450 parent source,parent.chosen.safe,?_,?_⟩
  · exact semantic_node_in_signature p.state.base p.root e localData.1 m fit.1
  · intro i
    have absent := i.isLt
    have no : p.root.demand.outputs = [] := parent.chosen.noOutputs
    simp [no] at absent

def GroupedEvidence (p : FullProblem) (m : I72.Model) (r : GroupedReport) : Prop :=
  ∃ x : InternalReport p, x.groups ≠ [] ∧ SameReport r (exactReport x) ∧ ParentMeaning p m x

inductive Report where
  | previous (result : GroupedEntry453.Report)
  | rawGrouped (result : GroupedReport)

inductive Witness where
  | previous (data : GroupedEntry453.Witness)
  | rawGrouped (data : SourceDiagnosticWire)

def check_full454 (p : FullProblem) : Report → Witness → Bool
  | .previous r, .previous w => GroupedEntry453.check_full453 p r w
  | .rawGrouped r, .rawGrouped w => check p r w
  | _, _ => false

theorem all_previous_witness_Bools_unchanged454 (p : FullProblem)
    (r : GroupedEntry453.Report) (w : GroupedEntry453.Witness) :
    check_full454 p (.previous r) (.previous w) = GroupedEntry453.check_full453 p r w := rfl

def ClassifiedAs (p : FullProblem) : Report → Prop
  | .previous r => GroupedEntry453.ClassifiedAs p r
  | .rawGrouped r => Exact p r

def ReportEvidence (p : FullProblem) (m : I72.Model) : Report → Prop
  | .previous r => GroupedEntry453.ReportEvidence p m r
  | .rawGrouped r => GroupedEvidence p m r

theorem check_full_sound454 (p : FullProblem) (r : Report) (w : Witness)
    (ok : check_full454 p r w = true) :
    ClassifiedAs p r ∧ ∀ m, FitsFull p.state m → ReportEvidence p m r := by
  cases r with
  | previous r =>
    cases w with
    | previous w => exact GroupedEntry453.check_full_sound453 p r w ok
    | rawGrouped w => cases ok
  | rawGrouped r =>
    cases w with
    | previous w => cases ok
    | rawGrouped w =>
      have classified := (exact_same_phase_report_iff_finite_wire454 p r).mp ⟨w,ok⟩
      obtain ⟨x,nonempty,same⟩ := classified
      exact ⟨⟨x,nonempty,same⟩,fun m fit =>
        ⟨x,nonempty,same,actual_parent_event_meaning_at_every_fit454 p x m fit⟩⟩

theorem independent_same_phase_report_has_cumulative_witness454
    (p : FullProblem) (r : GroupedReport) (h : Exact p r) :
    ∃ w, check_full454 p (.rawGrouped r) (.rawGrouped w) = true :=
  (exact_same_phase_report_iff_finite_wire454 p r).mpr h

end Yulang.GeneralDeclarativeI65.I72.WhereSites450.OriginalCohorts451.SamePhase454
