import Yulang.GeneralDeclarativeI65I74ProducerSingleVisible479
import Yulang.GeneralDeclarativeInlineFootprint331

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.Producer479

open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open ObservationAlternatives473 (Positions)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeWitnessOrigins350 (Attached attach)
open GeneralDeclarativeInlineTrace331 (Read)
open InputCoordinates475 (rawAt StampedRead SourceIndexPair478 FirstIs recoverOldStamps478
  PairedOldRows478 ordered_old_stamp_recovery_has_independent_exact_replay478)

private theorem stamp_existing_rows480 (raw authored : List Equation)
    (todo : List Equation) (inRaw : todo ⊆ raw) (inAuthored : todo ⊆ authored) :
    ∃ (ids : List SourceIndexPair478) (rows : List StampedRead),
      PairedOldRows478 raw authored ids rows ∧ rows.map StampedRead.row = todo := by
  induction todo with
  | nil => exact ⟨[],[],.nil,rfl⟩
  | cons e es tail =>
    obtain ⟨a,atRaw⟩ := List.mem_iff_getElem?.mp (inRaw (List.mem_cons_self (a := e) (l := es)))
    obtain ⟨b,atAuth⟩ := List.mem_iff_getElem?.mp (inAuthored (List.mem_cons_self (a := e) (l := es)))
    obtain ⟨ids,rows,stamped,erasure⟩ := tail
      (fun _ h => inRaw (List.mem_cons_of_mem e h))
      (fun _ h => inAuthored (List.mem_cons_of_mem e h))
    exact ⟨⟨a,b⟩ :: ids,⟨a,b,e⟩ :: rows,.cons rfl atRaw atAuth stamped,by simp [erasure]⟩

private theorem read_attached_exact480
    {p : FullProblem} {basis : PriorPhase} (a : Attached (rawAt p) basis.authors) :
    attach (rawAt p) basis.authors = some a := by
  have source : basis.authors.authored.all (fun x => decide (x ∈ (rawAt p).equations)) = true :=
    List.all_eq_true.mpr (fun _ member => decide_eq_true (a.authored member))
  have produced : basis.authors.produced.all (fun x => decide (x.1 ∈ (rawAt p).equations)) = true :=
    List.all_eq_true.mpr (fun x member => decide_eq_true (a.produced x member))
  simp [attach,source,produced]

/-- When no preselected coordinate list is recorded, the existential
witness may put the selected physical root first and then copy the
authored equations. The independent old read transports to that list.
This does not recover a discarded ordering in any actual execution. -/
theorem a_source_without_recorded_order_still_has_a_faithful_finite_wire480
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel} {basis : PriorPhase}
    (event : TypedInput p gd pos rel) (valid : basis.ExactFor event)
    (actualSource : event.support.derivesFrom event.rootRow .source)
    (actualKind : event.backing = .source actualSource)
    (absent : basis.recordedReads = none) :
    ∃ wire, IssueIsFaithful basis event wire := by
  have pre := valid
  unfold PriorPhase.ExactFor at pre
  rw [actualKind] at pre
  obtain ⟨⟨attached⟩,authoredExactly,oldRead,_⟩ := pre
  obtain ⟨a,atAuth⟩ := List.mem_iff_getElem?.mp ((authoredExactly _).mpr actualSource)
  obtain ⟨ids,tail,stamped,erasure⟩ := stamp_existing_rows480
    (rawAt p).equations basis.authors.authored basis.authors.authored
    (fun _ h => attached.authored h) (fun _ h => h)
  let head : StampedRead := ⟨event.rawOrdinal,a,event.rootRow⟩
  let addresses : List SourceIndexPair478 := ⟨event.rawOrdinal,a⟩ :: ids
  let rows : List StampedRead := head :: tail
  have accepted : recoverOldStamps478 (rawAt p).equations basis.authors.authored addresses =
      some rows := ordered_old_stamp_recovery_has_independent_exact_replay478.mpr
    (.cons (row := head) rfl event.existingRoot atAuth stamped)
  have first : FirstIs event.head.orig.capture.lower rows head := by
    refine ⟨event.rootOwns.1,[],tail,rfl,?_⟩
    intro x h
    cases h
  have read : Read ⟨(rawAt p).normal,rows.map StampedRead.row⟩ .actual
      (.variable event.head.orig.capture.lower) event.head.orig.code event.uses := by
    obtain ⟨footprint,inside,replay⟩ := GeneralDeclarativeInlineFootprint331.trace oldRead
    refine replay ⟨(rawAt p).normal,rows.map StampedRead.row⟩ rfl ?_
    intro eq present
    change eq ∈ (head :: tail).map StampedRead.row
    rw [List.map_cons,erasure]
    exact List.mem_cons_of_mem event.rootRow (inside present)
  obtain ⟨route,⟨arg,decl,atRoot,steps,sites⟩,ran⟩ :=
    single_input_reifies_a_route_even_without_any_producer479 event
  let data : AuthoredIssueData :=
    ⟨basis.authors,⟨event.report.rootArgument,addresses,event.report.outcome.1⟩,a⟩
  refine ⟨⟨route,.authored data⟩,⟨arg,decl,atRoot,steps,sites⟩,?_⟩
  rw [actualKind]
  refine ⟨rfl,rfl,rfl,atAuth,⟨?_,rows,accepted,⟨head,first,rfl,rfl⟩,read⟩,?_⟩
  · intro selected h
    rw [absent] at h
    cases h
  · have bit : checkAuthoredRoot p pos route data = true := by
      simp [checkAuthoredRoot,atRoot,event.physicalRow,event.existingRoot,data,atAuth]
    simp [readSourceIssueAtRoute,bit,read_attached_exact480 attached,
      data,accepted,ran,bind,Option.bind]

end Yulang.GeneralDeclarativeI65.I72.Producer479
