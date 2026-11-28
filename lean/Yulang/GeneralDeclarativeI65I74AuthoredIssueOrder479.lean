import Yulang.GeneralDeclarativeI65I74G04Producer479

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.Producer479
open InputCoordinates475 (rawAt StampedRead FirstIs SourceIndexPair478 first first_is_exact
  PairedOldRows478 recoverOldStamps478 recovery_never_reorders_original_pairs478
  ordered_old_stamp_recovery_has_independent_exact_replay478
  erasing_duplicate_row_payload_fields_loses_no_old_ordered_read478 first_uses_two_actual_coordinates)
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open ObservationAlternatives473 (Positions)
open GeneralDeclarativeInlineTrace331 (Read)

theorem an_issued_authored_trace_reads_the_exact_order_and_physical_root479
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel} {basis : PriorPhase}
    {event : TypedInput p gd pos rel} {data : AuthoredIssueData}
    (retained : AuthoredRunRetained basis event data) :
    ∃ (rows : List StampedRead) (head : StampedRead),
      rows.map StampedRead.indexPair478 = data.references.reads ∧
      PairedOldRows478 (rawAt p).equations basis.authors.authored data.references.reads rows ∧
      FirstIs event.head.orig.capture.lower rows head ∧
      head.raw = event.rawOrdinal ∧ head.author = data.rootAuthorOrdinal ∧
      head.row = event.rootRow ∧
      basis.authors.authored[data.rootAuthorOrdinal]? = some event.rootRow ∧
      Read ⟨(rawAt p).normal,rows.map StampedRead.row⟩ .actual
        (.variable event.head.orig.capture.lower) event.head.orig.code event.uses := by
  obtain ⟨rows,recovered,⟨head,chosen,rawIndex,authorIndex⟩,typed⟩ := retained.2
  have same := recovery_never_reorders_original_pairs478 recovered
  have checked := (erasing_duplicate_row_payload_fields_loses_no_old_ordered_read478 ..).mp
    (by rw [same]; exact recovered)
  obtain ⟨rawRow,authored,_⟩ := first_uses_two_actual_coordinates _ _ _ checked (first_is_exact.mpr chosen)
  have rootEq : head.row = event.rootRow := by
    rw [rawIndex,event.existingRoot] at rawRow
    exact (Option.some.inj rawRow).symm
  exact ⟨rows,head,same,ordered_old_stamp_recovery_has_independent_exact_replay478.mp recovered,
    chosen,rawIndex,authorIndex,rootEq,by simpa only [authorIndex,rootEq] using authored,typed⟩

theorem retained_pre_erasure_source_order_does_not_allow_an_empty_phase_trace479
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel} {basis : PriorPhase}
    {event : TypedInput p gd pos rel} {data : AuthoredIssueData}
    (retained : AuthoredRunRetained basis event data) :
    data.references.reads ≠ [] ∧
      ∀ previous, basis.recordedReads = some previous → data.references.reads = previous := by
  obtain ⟨rows,head,same,_,picked,_⟩ :=
    an_issued_authored_trace_reads_the_exact_order_and_physical_root479 retained
  refine ⟨?_,retained.1⟩
  intro none
  have empty : rows = [] := by simpa [none] using same
  obtain ⟨_,before,after,asList,_⟩ := picked
  rw [empty] at asList
  simp at asList

end Yulang.GeneralDeclarativeI65.I72.Producer479
