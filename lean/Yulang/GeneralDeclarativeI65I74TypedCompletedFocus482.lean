import Yulang.GeneralDeclarativeI65I74TypedWholeAuthoredFocus482
import Yulang.GeneralDeclarativeI65I74TypedVisibleRead482
import Yulang.GeneralDeclarativeI65I74BoundReleaseProducer479

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open Producer479 (PriorPhase ReleasedIssueData CompletedAssociation readBoundReleasedIssue readRoute)
open NativeProducer465 (CheckedPhase PhaseOriginAt)
open ObservationAlternatives473 (Positions oldPosition graphOf)
open QuotientObservation471 (ReturnsUpToEquality)
open InputCoordinates475 (rawAt SamePhaseInputObservation478)
open GeneralDeclarativeWitnessOrigins350 (Attached attach support)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeInlineTrace331 (realize)
open GeneralDeclarativeTermWalk322 (Walk)
open GeneralDeclarativeRepeatedActual323 (eqAt)
open GeneralNominalCenteredHeadMatExpressions (Expr)

/-- Computation-only projection of the currently authorized ordinary
input. The completion check always uses the original prior separately. -/
def visibleBasis (basis : PriorPhase) : PriorPhase :=
  ⟨visibleReadView basis.authors,[],none⟩

structure CompletedFocusWire (n : Nat) where
  focus : WholeAuthoredWire n
  ordinaryOwner : Nat
  producedOrdinal : Nat
  release : ReleasedIssueData

structure CompletedFocus {n : Nat} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n)) (basis : PriorPhase)
    (phase : CheckedPhase p.old.state.core) (w : CompletedFocusWire n) where
  attached : Attached (rawAt p) basis.authors
  focused : WholeAuthoredReceipt p gd pos rel (visibleBasis basis) w.focus
  exactRootRow : Equation
  exactRaw : (rawAt p).equations[focused.initial.initialIndices.raw]? = some exactRootRow
  exactOrigin : (visibleWithAuthority basis.authors)[focused.initial.initialIndices.author]? =
    some (.completed w.producedOrdinal w.ordinaryOwner,exactRootRow)
  output : SamePhaseInputObservation478
  releasedChecked : readBoundReleasedIssue p gd pos rel basis phase w.ordinaryOwner w.focus.route w.release = some output

private def withFound {T : Type} (o : Option T) : Option {a // o = some a} :=
  match o with | none => none | some x => some ⟨x,rfl⟩

def readCompletedFocus {n : Nat} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n)) (basis : PriorPhase)
    (phase : CheckedPhase p.old.state.core) (w : CompletedFocusWire n) :
    Option (CompletedFocus p gd pos rel basis phase w) := do
  let attached ← attach (rawAt p) basis.authors
  let focused ← readWholeAuthoredFocus p gd pos rel (visibleBasis basis) w.focus
  let row ← withFound ((rawAt p).equations[focused.initial.initialIndices.raw]?)
  if strong : (visibleWithAuthority basis.authors)[focused.initial.initialIndices.author]? =
      some (.completed w.producedOrdinal w.ordinaryOwner,row.val) then
    let bound ← withFound (readBoundReleasedIssue p gd pos rel basis phase w.ordinaryOwner w.focus.route w.release)
    pure ⟨attached,focused,row.val,row.property,strong,bound.val,bound.property⟩
  else none

theorem completed_focus_reads_same_ordinary_row_and_exact_active_native_release
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current} {pos : Positions n}
    {rel : List (Fin n × Fin n)} {basis : PriorPhase} {phase : CheckedPhase p.old.state.core}
    {w : CompletedFocusWire n} (accepted : CompletedFocus p gd pos rel basis phase w) :
    accepted.output = accepted.focused.initial.output ∧
    basis.authors.produced[w.producedOrdinal]? = some (accepted.exactRootRow,w.ordinaryOwner) ∧
    w.ordinaryOwner ∈ basis.authors.released ∧
    (⟨w.ordinaryOwner,accepted.focused.initial.initialIndices.raw,accepted.exactRootRow,
      w.release.write,w.release.originOrdinal⟩ : CompletedAssociation) ∈ basis.completed ∧
    PhaseOriginAt phase w.release.write accepted.exactRootRow.left w.release.originOrdinal := by
  obtain ⟨_,_,_,_,_,_,_,_,rawIndex,_,_,_,geometry⟩ := actual_root_pinned_read_iff.mp accepted.focused.bound
  obtain ⟨releaseRow,exactAt,association,released,run⟩ :=
    Producer479.exact_output_association_and_current_release_replay479.mp accepted.releasedChecked
  have sameRun := Option.some.inj (run.symm.trans geometry)
  have sameEq : releaseRow = accepted.exactRootRow := by
    change accepted.focused.initial.initialIndices.raw =
      (pos.cells.get w.focus.route.trail.cursor.which).oldOrdinal at rawIndex
    have picked := accepted.exactRaw
    rw [rawIndex] at picked
    exact Option.some.inj (exactAt.symm.trans picked)
  have storedInView : (visibleReadView basis.authors).authored[accepted.focused.initial.initialIndices.author]? =
      some accepted.exactRootRow := by
    rw [←visibleWithAuthority_erases_to_exact_input_view,List.getElem?_map,accepted.exactOrigin]
    rfl
  obtain ⟨authority,label,valid⟩ := each_projected_view_slot_has_original_ordinal_authority _ _ _ storedInView
  rw [accepted.exactOrigin] at label
  have exactLabel := congrArg Prod.fst (Option.some.inj label)
  change ReadRowAuthority.completed w.producedOrdinal w.ordinaryOwner = authority at exactLabel
  subst authority
  rw [sameEq] at association released
  change accepted.focused.initial.initialIndices.raw =
    (pos.cells.get w.focus.route.trail.cursor.which).oldOrdinal at rawIndex
  exact ⟨sameRun,valid.1,valid.2,rawIndex.symm ▸ association,released⟩

theorem same_completed_typed_input_and_signed_report_hold_in_every_original_fit
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current} {pos : Positions n}
    {rel : List (Fin n × Fin n)} {basis : PriorPhase} {phase : CheckedPhase p.old.state.core}
    {w : CompletedFocusWire n} (x : CompletedFocus p gd pos rel basis phase w) :
    (x.output.outcome.2.2.2 = true ↔
      ReturnsUpToEquality (graphOf p.old.state.core pos) x.focused.reportTrace.focus.finish.index) ∧
    ∃ rebuilt : Expr, (∀ m : Model, FitsFull p.state m →
      eqAt m.assignment (.variable x.focused.original.orig.capture.lower) rebuilt) ∧
      Walk .actual rebuilt x.focused.original.orig.code x.focused.initial.used := by
  have origin := completed_focus_reads_same_ordinary_row_and_exact_active_native_release x
  have visits := (pinned_signed_focus_reflects_same_trail_and_every_read x.focused.reportTrace).1
  have sign := (Producer479.declarative_trail_reads_existing_edges_and_returns_at_the_terminal479 visits).2
  refine ⟨origin.1.symm ▸ x.focused.sameBit.symm ▸ sign,?_⟩
  obtain ⟨_,head,_,_,_,headRead,_,_,_,_,_,checked,_⟩ := actual_root_pinned_read_iff.mp x.focused.bound
  have sameHead := Option.some.inj (headRead.symm.trans x.focused.atHead)
  subst head
  have supported := (read_with_genuine_completed_and_source_support_iff_finite_visible_read x.attached).mp ⟨_,checked⟩
  obtain ⟨rebuilt,meaning,walk⟩ := realize supported
  exact ⟨rebuilt,fun m f => meaning m.assignment f.1.1.1,walk⟩

end Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank
