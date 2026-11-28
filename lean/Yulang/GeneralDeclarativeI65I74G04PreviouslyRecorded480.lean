import Yulang.GeneralDeclarativeI65I74G04ProducerMeaning479
import Yulang.GeneralDeclarativeI65I74ProducerSingleVisible479

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.Producer479
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open ObservationAlternatives473 (Positions)
open NativeProducer465 (CheckedPhase PhaseOriginAt finite_phase_origin_check_iff_literal_placed_active_row)
open GeneralDeclarativeWitnessNativeValue360 (Write)
open GeneralDeclarativeWitnessOrigins350 (Attached attach)
open InputCoordinates475 (rawAt StampedRead first_is_exact first_uses_two_actual_coordinates
  erasing_duplicate_row_payload_fields_loses_no_old_ordered_read478 recovery_never_reorders_original_pairs478)

private theorem an_attached_manifest_is_exactly_read480
    {p : FullProblem} {basis : PriorPhase} (a : Attached (rawAt p) basis.authors) :
    attach (rawAt p) basis.authors = some a := by
  have source : basis.authors.authored.all (fun x => decide (x ∈ (rawAt p).equations)) = true :=
    List.all_eq_true.mpr (fun _ member => decide_eq_true (a.authored member))
  have produced : basis.authors.produced.all (fun x => decide (x.1 ∈ (rawAt p).equations)) = true :=
    List.all_eq_true.mpr (fun x member => decide_eq_true (a.produced x member))
  simp [attach,source,produced]

/-- Reification of a source log which the actual input stage has already
recorded. This does not establish that the stage retains any source log. -/
theorem a_recorded_pre_erasure_source_order_has_a_faithful_finite_replay480
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel} {basis : PriorPhase}
    (event : TypedInput p gd pos rel) (valid : basis.ExactFor event)
    (actualSource : event.support.derivesFrom event.rootRow .source)
    (actualKind : event.backing = .source actualSource)
    {recorded} (old : basis.recordedReads = some recorded) :
    ∃ wire, IssueIsFaithful basis event wire := by
  have pre := valid
  unfold PriorPhase.ExactFor at pre
  rw [actualKind] at pre
  obtain ⟨⟨attached⟩,_,_,trace⟩ := pre
  obtain ⟨rows,retained,⟨root,selected,rawIndex⟩,typed⟩ := trace _ old
  obtain ⟨route,⟨arg,decl,atRoot,steps,sites⟩,ran⟩ :=
    single_input_reifies_a_route_even_without_any_producer479 event
  have same := recovery_never_reorders_original_pairs478 retained
  have validRows := (erasing_duplicate_row_payload_fields_loses_no_old_ordered_read478 ..).mp
    (by rw [same]; exact retained)
  have ⟨raw,authored,_⟩ :=
    first_uses_two_actual_coordinates _ _ _ validRows (first_is_exact.mpr selected)
  have rootEq : root.row = event.rootRow := by
    rw [rawIndex,event.existingRoot] at raw
    exact (Option.some.inj raw).symm
  have auth : basis.authors.authored[root.author]? = some event.rootRow := by
    simpa only [rootEq] using authored
  let data : AuthoredIssueData :=
    ⟨basis.authors,⟨event.report.rootArgument,recorded,event.report.outcome.1⟩,root.author⟩
  refine ⟨⟨route,.authored data⟩,⟨arg,decl,atRoot,steps,sites⟩,?_⟩
  rw [actualKind]
  refine ⟨rfl,rfl,rfl,auth,⟨?_,rows,retained,⟨root,selected,rawIndex,rfl⟩,typed⟩,?_⟩
  · intro fixed h
    exact Option.some.inj (old.symm.trans h)
  · have bit : checkAuthoredRoot p pos route data = true := by
      simp [checkAuthoredRoot,atRoot,event.physicalRow,event.existingRoot,data,auth]
    simp [readSourceIssueAtRoute,bit,an_attached_manifest_is_exactly_read480 attached,
      data,retained,ran,bind,Option.bind]


/-- A genuinely retained release and its separately retained exact old
association can already be replayed, without originating either record. -/
theorem a_bound_released_fact_has_faithful_replay_without_issuing_it480
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel} {basis : PriorPhase}
    (event : TypedInput p gd pos rel) (valid : basis.ExactFor event)
    {owner : Nat} {phase : CheckedPhase p.old.state.core} {write : Write} {oldIndex : Nat}
    (out : event.support.derivesFrom event.rootRow (.output owner))
    (completed : event.settled owner)
    (actual : PhaseOriginAt phase write event.rootRow.left oldIndex)
    (chosen : event.backing = .released owner phase write oldIndex out completed actual) :
    ∃ wire, IssueIsFaithful basis event wire := by
  have pre := valid
  unfold PriorPhase.ExactFor at pre
  rw [chosen] at pre
  obtain ⟨route,⟨arg,decl,atRoot,steps,sites⟩,ran⟩ :=
    single_input_reifies_a_route_even_without_any_producer479 event
  let data : ReleasedIssueData := ⟨write,oldIndex⟩
  refine ⟨⟨route,.released data⟩,⟨arg,decl,atRoot,steps,sites⟩,?_⟩
  rw [chosen]
  refine ⟨rfl,rfl,pre,?_⟩
  have bit : checkReleasedRoot p pos phase route data = true := by
    simp [checkReleasedRoot,atRoot,event.physicalRow,event.existingRoot,data,
      (finite_phase_origin_check_iff_literal_placed_active_row ..).mpr actual]
  simp [readReleasedIssueAtRoute,bit,ran]


end Yulang.GeneralDeclarativeI65.I72.Producer479
