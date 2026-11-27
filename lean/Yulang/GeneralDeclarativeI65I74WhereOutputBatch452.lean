import Yulang.GeneralDeclarativeI65I74WhereOutputPairRead452

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.WhereSites450.OriginalCohorts451.OutputPhase452
open Yulang.GeneralDeclarativeI65
open RetainedFull445
open GeneralDeclarativeCaptureClosure320 (withOrdinary)

/-- Enumerates all ordered pairs of actual same-class requests for a
verification batch. This is not a merge scheduler and does not elect
one of these two source occurrences as a report position. -/
def verifiedEmissionPairs452 {p : FullProblem} {a : ParentSelection p.old}
    (d : OriginalDiagnostic a) : List (ActualPair (p := p) d) :=
  let slots := List.range d.marks.length
  slots.flatMap fun i => slots.filterMap fun j => readActualPhasePair452 d i j

theorem all_actual_pairs_are_in_verified_emission_batch452 {p : FullProblem}
    {a : ParentSelection p.old} {d : OriginalDiagnostic a} (x : ActualPair (p := p) d) :
    x ∈ verifiedEmissionPairs452 d := by
  have smaller := (generated_group_has_exact_source_order451 d x.genuine).2.2
  have li := mark_is_read_at_its_own_source_ordinal452 d (smaller.subset x.inLeft)
  have ri := mark_is_read_at_its_own_source_ordinal452 d (smaller.subset x.inRight)
  exact List.mem_flatMap.mpr ⟨x.left.ordinal,List.mem_range.mpr
    (List.getElem?_eq_some_iff.mp li).choose,
    List.mem_filterMap.mpr ⟨x.right.ordinal,List.mem_range.mpr
      (List.getElem?_eq_some_iff.mp ri).choose,
      actual_pairs_at_exact_original_ordinals_have_finite_read452 x⟩⟩

theorem actual_complete_pair_batch_only_checks_real_same_input_and_writes_nothing452
    {p : FullProblem} {a : ParentSelection p.old} (d : OriginalDiagnostic a) :
    (∀ x ∈ verifiedEmissionPairs452 d,
      GeneralNominalDemandMerging.SameInputs (allAssignments p.state) x.first.site x.second.site) ∧
    emissionRows (verifiedEmissionPairs452 d) = [] ∧
    withOrdinary p.state.base.core.current.ordinary (emissionRows (verifiedEmissionPairs452 d)) =
      p.state.base.core.current.ordinary := by
  refine ⟨fun x _ => (each_emission_pair_is_authorized_and_writes_nothing452 x).1,?_⟩
  exact output_equation_substep_exactly_preserves_raw_input452 (verifiedEmissionPairs452 d)

theorem checked_batch_internal_report_is_exactly_for_its_same_phase452 {p : FullProblem}
    (r : InternalK2452.InternalReport p) (m : OriginalMark) (known : m ∈ r.original.diagnostics.marks) :
    GeneralDeclarativePriority321.RootRecurs
      (withOrdinary p.state.base.core.current.ordinary
        (emissionRows (verifiedEmissionPairs452 r.original.diagnostics))) m.request.demand ↔
      InternalK2452.HasExactlyOneCyclicGroup r.original.diagnostics m :=
  InternalK2452.emission_phase_preserves_each_actual_K2_and_its_internal_entry452
    (verifiedEmissionPairs452 r.original.diagnostics) known

end Yulang.GeneralDeclarativeI65.I72.WhereSites450.OriginalCohorts451.OutputPhase452
