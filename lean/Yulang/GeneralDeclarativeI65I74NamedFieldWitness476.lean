import Yulang.GeneralDeclarativeI65I74ExactNamedEdge476

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open GeneralDeclarativeWitnessOrigins350 (Table Attached)
open ObservationAlternatives473 (Positions graphOf)
open LiteralVisits473 (Checkpoint GuardedObservationInput)
open QuotientObservation471 (ReturnsUpToEquality)
open CommonRoleRegularGraph (successors)

/-- Reify the existing trace occurrence to a finite literal list index.
The choice is given by an independently fixed old typed receipt, not
inferred from a shared child name or from the marked capture's values. -/
theorem independently_given_actual_exposure_yields_a_finite_field_wire476
    {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} (fixed : FixedFieldChoice476 r)
    {trace : LocatedCapture476 w.offered} (ran : readLocatedAtHead476 r = some trace)
    {mark : LocatedMark476 w.offered} (visited : mark ∈ trace.marks)
    (coord : mark.path = [.field fixed.label])
    (same : fixed.original.actualPayload = .variable mark.exposure.name) :
    ∃ ordinal, ∃ selected : NamedSelection476 r ⟨fixed.label,fixed.path,ordinal⟩,
      readNamedAtFixedChoice476 fixed ⟨fixed.label,fixed.path,ordinal⟩ = some selected ∧
      selected.mark = mark ∧ selected.trace = trace := by
  obtain ⟨ordinal,whereAt⟩ := List.mem_iff_getElem?.mp visited
  let selected : NamedSelection476 r ⟨fixed.label,fixed.path,ordinal⟩ :=
    ⟨fixed.original,trace,ran,mark,whereAt,coord,same⟩
  exact ⟨ordinal,selected,
    (fixed_named_join_is_exact_same_literal_field_receipt476 fixed _ selected).mpr ⟨rfl,rfl,HEq.rfl⟩,
    rfl,rfl⟩

theorem actual_named_field_and_safe_outer_reify_exact_finite_report476
    {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} (fixed : FixedFieldChoice476 r)
    {trace : LocatedCapture476 w.offered} (ran : readLocatedAtHead476 r = some trace)
    {mark : LocatedMark476 w.offered} (visited : mark ∈ trace.marks)
    (coord : mark.path = [.field fixed.label])
    (same : fixed.original.actualPayload = .variable mark.exposure.name)
    {table : Positions n} {rel : List (Fin n × Fin n)} {outer inner : Fin n}
    (op : atNamedCell476 table outer r.head.orig.capture.lower r.picked.raw)
    (ip : atNamedCell476 table inner mark.exposure.name mark.exposure.picked.raw)
    (outside : GuardedObservationInput p.old.state.core table rel outer)
    (inside : GuardedObservationInput p.old.state.core table rel inner)
    (safe : ¬ ReturnsUpToEquality (graphOf p.old.state.core table) outer)
    (b : Bool) (sign : b = true ↔ ReturnsUpToEquality (graphOf p.old.state.core table) inner) :
    ∃ (ordinal : Nat) (first last : Checkpoint n),
      first.which = outer ∧ last.which = inner ∧
      ∃ answer : NamedFieldQuotient476 fixed ⟨fixed.label,fixed.path,ordinal⟩ table rel first last,
        readNamedFieldQuotient476 fixed ⟨fixed.label,fixed.path,ordinal⟩ table rel first last = some answer ∧
        answer.report = ⟨p.root.occurrence,r.head.orig.declaration.id,w.frame.sourceOrdinal,
          fixed.path,fixed.label,b⟩ ∧
        inner ∈ successors (graphOf p.old.state.core table) outer := by
  obtain ⟨ix,chosen,checked,chosenExact,_⟩ :=
    independently_given_actual_exposure_yields_a_finite_field_wire476 fixed ran visited coord same
  have choice := (fixed_named_join_is_exact_same_literal_field_receipt476 fixed _ chosen).mp checked
  have exactMark : atNamedCell476 table inner chosen.mark.exposure.name chosen.mark.exposure.picked.raw := by
    rw [chosenExact]
    exact ip
  obtain ⟨first,last,atFirst,atLast,answer,returned,report⟩ :=
    checked_named_field_has_a_finite_exact_report_when_both_cones_are_given476
      chosen choice op exactMark outside inside safe b sign
  refine ⟨ix,first,last,atFirst,atLast,answer,returned,report,?_⟩
  simpa only [atFirst,atLast] using exact_named_field_is_an_original_outer_graph_edge476 answer

end Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
