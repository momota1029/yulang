import Yulang.GeneralDeclarativeI65I74OriginalRoster485
import Yulang.GeneralDeclarativeI65I74ProducerTrail479
import Yulang.GeneralDeclarativeI65I74TypedRootSafety482

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open RetainedFull445 (FullProblem)
open GeneralDeclarations (Declaration)
open PreparedDeclarations463 (CheckedTable HeadAddress PrecheckedHead readPrecheckedHead)
open Producer479 (Site Trail TrailWire readTrail)
open ObservationAlternatives473 (Positions oldPosition graphOf readTermAt)
open QuotientObservation471 (ReturnsUpToEquality)
open LiteralVisits473 (StepWire GuardedObservationInput)
open TypedRootSafety482 (AllRootSafe noRootReturnBool allRootCheckSound)
open LiteralVisits473 (Checkpoint readCheck)

/-- A local positive visit is relative to the original multi-candidate
roster. It is not a full match judgement or an all-negative certificate. -/
structure CandidatePathWire485 (n : Nat) where
  headArgument : Nat
  trail : TrailWire n

structure CandidatePath485 {n : Nat} (p : FullProblem)
    (gd : CheckedTable p.old.state.core.current) (pos : Positions n) (rel : List (Fin n × Fin n))
    (visibleIndex : Nat) (w : CandidatePathWire485 n) where
  authoredOrdinal : Nat
  head : PrecheckedHead (p := p.old) gd
  exactSlot : OriginalRosterCell485 p visibleIndex (authoredOrdinal,head.orig.declaration)
  exactAddress : head.orig.location = ⟨visibleIndex,w.headArgument⟩
  first : Site p.old.state.core pos
  samePattern : first.pattern = head.orig.original
  sameQuery : first.query = head.orig.code
  atPoint : oldPosition pos first.index = .logical head.orig.capture.lower
  last : Site p.old.state.core pos
  terminalBit : Bool
  visited : Trail p.old.state.core pos rel first (w.trail.tail.map Prod.fst)
    (w.trail.tail.map (fun pair => pair.2.which)) last terminalBit
  originalCursor : w.trail.cursor.which = first.index

def readCandidatePath485 {n : Nat} (p : FullProblem)
    (gd : CheckedTable p.old.state.core.current) (pos : Positions n) (rel : List (Fin n × Fin n))
    (visibleIndex : Nat) (w : CandidatePathWire485 n) :
    Option (CandidatePath485 p gd pos rel visibleIndex w) :=
  match original : rosterCell485 p visibleIndex with
  | none => none
  | some (ordinal,d) => do
    let head ← readPrecheckedHead (p := p.old) gd ⟨visibleIndex,w.headArgument⟩
    if address : head.orig.location = ⟨visibleIndex,w.headArgument⟩ then
      if equal : head.orig.declaration = d then
        let i := w.trail.cursor.which
        if atPoint : oldPosition pos i = .logical head.orig.capture.lower then
          match looked : readTermAt p.old.state.core pos i with
          | none => none
          | some term =>
            let first : Site p.old.state.core pos := ⟨i,head.orig.original,head.orig.code,term,looked⟩
            match result : readTrail rel first w.trail with
            | some (last,bit) =>
              have exact := Producer479.finite_trail_wire_reflects_exact_selected_path479 result
              have cell := (roster_cell_reads_exactly_its_two_original_slots485 _ _ _).mp original
              some ⟨ordinal,head,equal.symm ▸ cell,address,first,rfl,rfl,atPoint,last,bit,exact.2,exact.1⟩
            | none => none
        else none
      else none
    else none

theorem reported_candidate_positive_owns_the_exact_original_ordinal_and_site485
    {n} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {i w}
    (read : CandidatePath485 p gd pos rel i w) (yes : read.terminalBit = true)
    (nonempty : w.trail.tail ≠ []) :
    (declared485 p)[read.authoredOrdinal]? = some read.head.orig.declaration ∧
    (visible485 p)[i]? = some read.head.orig.declaration ∧
    ReturnsUpToEquality (graphOf p.old.state.core pos) read.last.index ∧
    w.trail.tail ≠ [] := by
  have same := (Producer479.declarative_trail_reads_existing_edges_and_returns_at_the_terminal479 read.visited).2
  exact ⟨read.exactSlot.2.2,read.exactSlot.1,same.mp yes,nonempty⟩

theorem independently_guarded_candidate_path_has_a_finite_wire_at_its_same_roster_slot485
    {n : Nat} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n))
    (i ord : Nat) (head : PrecheckedHead (p := p.old) gd)
    (index : head.orig.location.visibleOrdinal = i)
    (slot : OriginalRosterCell485 p i (ord,head.orig.declaration))
    (first last : Site p.old.state.core pos) (moves : List StepWire) (points : List (Fin n)) (bit : Bool)
    (startPattern : first.pattern = head.orig.original) (startQuery : first.query = head.orig.code)
    (root : oldPosition pos first.index = .logical head.orig.capture.lower)
    (actual : Trail p.old.state.core pos rel first moves points last bit) :
    ∃ w : CandidatePathWire485 n, ∃ read : CandidatePath485 p gd pos rel i w,
      readCandidatePath485 p gd pos rel i w = some read ∧ read.authoredOrdinal = ord ∧
      read.head = head ∧ read.first = first ∧ read.last = last ∧ read.terminalBit = bit ∧
      w.trail.tail.map Prod.fst = moves ∧ w.trail.tail.map (fun pair => pair.2.which) = points := by
  obtain ⟨wire,cursor,steps,oldPoints,ran⟩ := Producer479.finite_trail_wire_replays_exact_selected_path479 actual
  let w : CandidatePathWire485 n := ⟨head.orig.location.headArgument,wire⟩
  have loc : head.orig.location = ⟨i,w.headArgument⟩ := by
    cases seen : head.orig.location
    simp [seen,w] at index ⊢
    exact index
  have prepared : readPrecheckedHead (p := p.old) gd ⟨i,w.headArgument⟩ = some head := by
    rw [←loc]
    exact PreparedDeclarations463.each_prechecked_head_position_replays gd head
  have source := (roster_cell_reads_exactly_its_two_original_slots485 _ _ _).mpr slot
  have whereFrom : oldPosition pos w.trail.cursor.which = .logical head.orig.capture.lower := cursor ▸ root
  have term : readTermAt p.old.state.core pos w.trail.cursor.which = some first.term := cursor ▸ first.exactTerm
  have firstEq : (⟨w.trail.cursor.which,head.orig.original,head.orig.code,first.term,term⟩ :
      Site p.old.state.core pos) = first := by
    cases first with
    | mk atFirst pattern query raw exact =>
      change pattern = head.orig.original at startPattern
      change query = head.orig.code at startQuery
      change w.trail.cursor.which = atFirst at cursor
      cases startPattern
      cases startQuery
      cases cursor
      rfl
  refine ⟨w,?_⟩
  unfold readCandidatePath485
  simp only [prepared,bind,Option.bind,loc,dite_true,whereFrom]
  split
  · rename_i missing
    rw [source] at missing
    cases missing
  · rename_i ordinal declaration viewed
    have equal := Option.some.inj (viewed.symm.trans source)
    cases equal
    simp only [dite_true]
    split
    · rename_i missing
      rw [term] at missing
      cases missing
    · rename_i found observed
      have same := Option.some.inj (observed.symm.trans term)
      subst found
      split
      · rename_i terminal reading checked
        have same : (terminal,reading) = (last,bit) := Option.some.inj
          (checked.symm.trans (firstEq.symm ▸ ran))
        cases same
        exact ⟨_,rfl,rfl,rfl,firstEq,rfl,rfl,steps,oldPoints⟩
      · rename_i failed
        have ranExact := firstEq.symm ▸ ran
        rw [failed] at ranExact
        cases ranExact

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
