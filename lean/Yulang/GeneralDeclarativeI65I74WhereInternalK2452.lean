import Yulang.GeneralDeclarativeI65I74WhereOutputPhase452

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.WhereSites450.OriginalCohorts451.InternalK2452
open Yulang.GeneralDeclarativeI65
open RetainedFull445
open OutputPhase452
open GeneralDeclarativeCaptureClosure320 (withOrdinary)

/-- A group is kept exactly once if its checked raw root is cyclic.
The order within each group is literal source order. No field is a
preferred source location; the temporary key is not a diagnostic code. -/
def internalCyclicGroups {p : Checker408.Problem} {a : ParentSelection p}
    (d : OriginalDiagnostic a) : List CohortOrigins :=
  d.cohortsWithOrigins.filter fun g => g.marks.any OriginalMark.rawK2

theorem cyclic_groups_keep_unique_keys452 {p : Checker408.Problem} {a : ParentSelection p}
    (d : OriginalDiagnostic a) :
    ((internalCyclicGroups d).map CohortOrigins.key).Nodup := by
  apply List.Sublist.nodup (List.Sublist.map CohortOrigins.key List.filter_sublist)
  simpa [OriginalDiagnostic.cohortsWithOrigins,List.map_map,Function.comp_def] using
    class_key_list_has_no_repeated_class451 (d.marks.map OriginalMark.classLabel)

theorem marked_bit_exact_current_root452 {p : Checker408.Problem} {a : ParentSelection p}
    (d : OriginalDiagnostic a) {m : OriginalMark} (seen : m ∈ d.marks) :
    m.rawK2 = true ↔ RootCycle p.state m.request := by
  obtain ⟨request,_,flag⟩ := any_mark_is_actual_original_diagnostic451 d seen
  obtain ⟨b,stored,exact⟩ := status_position_is_actual_child451 d.status m.ordinal request
  cases Option.some.inj (flag.symm.trans stored)
  exact exact

theorem one_checked_entry_means_K2_at_every_original452 {p : Checker408.Problem}
    {a : ParentSelection p} (d : OriginalDiagnostic a) {g : CohortOrigins}
    (entry : g ∈ internalCyclicGroups d) :
    g.marks = d.atClass g.key ∧ g.marks ≠ [] ∧
      g.marks.Sublist d.marks ∧ ∀ m ∈ g.marks, RootCycle p.state m.request := by
  obtain ⟨source,nonempty⟩ := List.mem_filter.mp entry
  obtain ⟨m,first,cycle⟩ := List.any_eq_true.mp nonempty
  obtain ⟨same,inhabited,ordered⟩ := generated_group_has_exact_source_order451 d source
  refine ⟨same,inhabited,ordered,?_⟩
  intro n next
  have bit := all_original_members_of_each_group_share_actual_raw_K2451 d source first next
  exact (marked_bit_exact_current_root452 d (ordered.subset next)).mp (bit.symm.trans cycle)

def HasExactlyOneCyclicGroup {p : Checker408.Problem} {a : ParentSelection p}
    (d : OriginalDiagnostic a) (m : OriginalMark) : Prop :=
  ∃ g, (g ∈ internalCyclicGroups d ∧ m ∈ g.marks) ∧
    ∀ h, h ∈ internalCyclicGroups d ∧ m ∈ h.marks → h = g

theorem actual_cycle_has_exactly_one_internal_diagnostic452 {p : Checker408.Problem}
    {a : ParentSelection p} (d : OriginalDiagnostic a) {m : OriginalMark}
    (seen : m ∈ d.marks) :
    RootCycle p.state m.request ↔ HasExactlyOneCyclicGroup d m := by
  constructor
  · intro cycle
    obtain ⟨⟨g,group,x⟩,unique⟩ := every_raw_original_occurrence_is_in_exactly_one_group451 d seen
    refine ⟨g,⟨List.mem_filter.mpr ⟨group,List.any_eq_true.mpr
      ⟨m,x,(marked_bit_exact_current_root452 d seen).mpr cycle⟩⟩,x⟩,?_⟩
    rintro h ⟨included,y⟩
    exact unique h g (List.mem_filter.mp included).1 group y x
  · rintro ⟨g,⟨entry,mark⟩,_⟩
    exact (one_checked_entry_means_K2_at_every_original452 d entry).2.2.2 m mark

theorem emission_phase_preserves_each_actual_K2_and_its_internal_entry452 {p : FullProblem}
    {a : ParentSelection p.old} {d : OriginalDiagnostic a}
    (xs : List (ActualPair (p := p) d)) {m : OriginalMark} (seen : m ∈ d.marks) :
    GeneralDeclarativePriority321.RootRecurs
      (withOrdinary p.state.base.core.current.ordinary (emissionRows xs)) m.request.demand ↔
      HasExactlyOneCyclicGroup d m := by
  rw [(output_equation_substep_exactly_preserves_raw_input452 xs).2]
  exact actual_cycle_has_exactly_one_internal_diagnostic452 d seen

structure InternalReport (p : FullProblem) where
  original : AnnotatedOriginalDiagnostics p.old

def InternalReport.groups {p : FullProblem} (r : InternalReport p) : List CohortOrigins :=
  internalCyclicGroups r.original.diagnostics

/-- Same FullProblem; grouping is an internal checked projection, not
a change to check_full450 and not a compressed original WhereForest. -/
def readInternalReport452 (p : FullProblem) (w : SourceDiagnosticWire) : Option (InternalReport p) :=
  (readOriginalWhereProfiles451 p w).map fun original => ⟨original⟩

theorem independent_scoped_internal_report_has_finite_replay452 (p : FullProblem)
    (r : InternalReport p) : ∃ w, readInternalReport452 p w = some r := by
  obtain ⟨w,selected⟩ := independent_selected_original_profiles_have_finite_wire451 p r.original
  cases r
  exact ⟨w,by simp [readInternalReport452,selected]⟩

end Yulang.GeneralDeclarativeI65.I72.WhereSites450.OriginalCohorts451.InternalK2452
