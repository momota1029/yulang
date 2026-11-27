import Yulang.GeneralDeclarativeI65I74PreparedLocatedReport463
import Yulang.GeneralDeclarativeI65I74ExistingInspectedOrigins463

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.PreparedDeclarations463
open EligibleFieldStart461 WrittenPattern460 PhysicalVisit463
open WrittenPattern460.PhysicalOrigin
open GeneralDeclarativeGraphRows321 (observed)
open GeneralDeclarativeK2Alias321 (AliasCycle)

private theorem coordinate_end_term_is_unique {keys root t path n m u v}
    (a : CoordinateWalk keys root t path n u) (b : CoordinateWalk keys root t path m v) : u = v := by
  have ha := (selected_coordinates_iff_independent_walk (coordinate_walk_last_original_cell a)).mpr a
  have hb := (selected_coordinates_iff_independent_walk (coordinate_walk_last_original_cell b)).mpr b
  exact Option.some.inj (ha.symm.trans hb)

/-- Same resolved OriginalAnchor is used for lexical provenance and for
the graph/model trail. No separately supplied alias or display location. -/
theorem exact_located_original_paths_and_rows_hold_in_every_same_fit
    {input : Input} {l : LocatedReport} (exact : ExactLocated input l)
    (m : I72.Model) (fit : I72.FitsFull input.problem.state m) :
    ∃ (a : EligibleStart input.problem.old) (last : Term),
      PreparedSource input.checked a ∧
      exactReport a.anchor l.report.path l.report.terminal = l.report ∧
      IndexedSourceFit input.problem.old.state.core m
        (fun _ => queryKeys input.problem.old.state.core) a.argument.lower
        (normalized (readTerm a.original)) a.query l.report.path l.equations l.report.terminal last l.mark ∧
      l.literal ≠ [] ∧
      (∀ pos p, (pos,p) ∈ l.literal →
        atSource a.original pos = some p ∧ readTerm (GeneralDeclarationPatterns.normalize p) = last) ∧
      AliasCycle input.problem.old.state.core.current.ordinary
        (observed input.problem.old.state.core.current.ordinary) l.report.terminal := by
  obtain ⟨⟨a,last,auth,trail,_,cycle,eq⟩,e,lit⟩ := exact
  have same : e = a := same_eligible_original_anchor_keeps_all_start_data
    (actual_source_anchor_is_determined_by_its_positions_in_same_problem rfl)
  subst e
  have joint := erase_indices_preserves_an_identical_authorized_trail trail
  have normalizedStart := anchor_compiles_the_normalized_original a.anchor
  have compiled := descend_actual_compiler_alignment normalizedStart joint
  have scope := full_trace_reflects_exact_compiled_scope compiled
  have normalizedEq : normalized (readTerm a.original) =
      readTerm (GeneralDeclarationPatterns.normalize a.original) :=
    normalized_of_original a.original
  change ScopedRaw input.problem.old.state.core a.argument.lower
    (normalized (readTerm a.original)) a.query l.report.path l.report.terminal last l.mark at scope
  rw [normalizedEq] at scope
  obtain ⟨pos,term,member,_,_⟩ :=
    existing_scoped_raw_route_has_finite_literal_origin a.original a.compiled scope
  refine ⟨a,last,auth,eq,all_same_fits_preserve_native_proof_on_each_identical_physical_row trail m fit.1,?_,?_,cycle⟩
  · intro empty
    rw [← lit,empty] at member
    cases member
  · intro pos found member
    rw [lit] at member
    obtain ⟨atWritten,_,path⟩ := whole_route_is_literal_and_preserves_exact_coordinates
      (route_occurrences_exact.mp member)
    have another := joint_has_exact_written_path joint
    rw [normalizedEq] at another
    exact ⟨atWritten,coordinate_end_term_is_unique path another⟩

theorem successful_located_witness_preserves_every_existing_authentic_origin
    {input : Input} {l : LocatedReport} {w : PreparedWire input}
    (read : readLocated w = some l) : ExactLocated input l :=
  (exact_located_report_iff_same_original_finite_wire ..).mpr ⟨w,read⟩

end Yulang.GeneralDeclarativeI65.I72.PreparedDeclarations463
