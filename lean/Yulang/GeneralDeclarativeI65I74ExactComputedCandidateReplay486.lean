import Yulang.GeneralDeclarativeI65I74CandidateSignedPath485

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable PrecheckedHead readPrecheckedHead)
open Producer479 (Site TrailWire readTrail)
open ObservationAlternatives473 (Positions oldPosition readTermAt)

/-- A packet computed from old coordinates is checked verbatim; a
different reified packet is not substituted in its place. -/
theorem the_exact_computed_wire_replays_on_the_same_original_candidate_slot486
    {n : Nat} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n))
    (i ord : Nat) (head : PrecheckedHead (p := p.old) gd)
    (index : head.orig.location.visibleOrdinal = i)
    (slot : OriginalRosterCell485 p i (ord,head.orig.declaration))
    (first last : Site p.old.state.core pos) (bit : Bool) (wire : TrailWire n)
    (startPattern : first.pattern = head.orig.original) (startQuery : first.query = head.orig.code)
    (root : oldPosition pos first.index = .logical head.orig.capture.lower)
    (cursor : wire.cursor.which = first.index) (ran : readTrail rel first wire = some (last,bit)) :
    let w : CandidatePathWire485 n := ⟨head.orig.location.headArgument,wire⟩
    ∃ read : CandidatePath485 p gd pos rel i w,
      readCandidatePath485 p gd pos rel i w = some read ∧ read.authoredOrdinal = ord ∧
      read.head = head ∧ read.first = first ∧ read.last = last ∧ read.terminalBit = bit := by
  let w : CandidatePathWire485 n := ⟨head.orig.location.headArgument,wire⟩
  change ∃ read : CandidatePath485 p gd pos rel i w,
    readCandidatePath485 p gd pos rel i w = some read ∧ read.authoredOrdinal = ord ∧
    read.head = head ∧ read.first = first ∧ read.last = last ∧ read.terminalBit = bit
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
        exact ⟨_,rfl,rfl,rfl,firstEq,rfl,rfl⟩
      · rename_i failed
        have ranExact := firstEq.symm ▸ ran
        rw [failed] at ranExact
        cases ranExact

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
