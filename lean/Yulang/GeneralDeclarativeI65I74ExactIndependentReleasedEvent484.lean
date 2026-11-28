import Yulang.GeneralDeclarativeI65I74ExactIndependentSourceEvent484
import Yulang.GeneralDeclarativeI65I74CompletedInterior484

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.Producer479
open RetainedFull445 (FullProblem)
open ObservationAlternatives473 (Positions graphOf)
open PreparedDeclarations463 (CheckedTable)
open SourceExposure481.ClosedBank
open NativeProducer465 (CheckedPhase PhaseOriginAt)
open GeneralDeclarativeWitnessNativeValue360 (Write)
open InputCoordinates475 (rawAt)
open LiteralVisits473 (Checkpoint)
open TypedRootSafety482 (AllRootSafe requestRootCheckSound)
open QuotientObservation471 (ReturnsUpToEquality)

def IsExactReleasedInput {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel} (e : TypedInput p gd pos rel)
    (owner : Nat) (phase : CheckedPhase p.old.state.core) (write : Write) (originOrdinal : Nat) : Prop :=
  match e.backing with
  | .source _ => False
  | .released own atPhase issued physical _ _ _ =>
    own = owner ∧ atPhase = phase ∧ issued = write ∧ physical = originOrdinal

theorem original_completed_input_retains_its_independent_active_origin
    {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel} (e : TypedInput p gd pos rel)
    (prior : PriorPhase) (owner : Nat) (phase : CheckedPhase p.old.state.core)
    (write : Write) (ordinal : Nat)
    (qualified : prior.ExactFor e) (same : IsExactReleasedInput e owner phase write ordinal) :
    e.support.derivesFrom e.rootRow (.output owner) ∧ e.settled owner ∧
      (⟨owner,e.rawOrdinal,e.rootRow,write,ordinal⟩ : CompletedAssociation) ∈ prior.completed ∧
      PhaseOriginAt phase write e.rootRow.left ordinal := by
  cases arm : e.backing with
  | source =>
    unfold IsExactReleasedInput at same
    rw [arm] at same
    exact same.elim
  | released actual atPhase placed native support settled active =>
    unfold IsExactReleasedInput at same
    rw [arm] at same
    obtain ⟨rfl,rfl,rfl,rfl⟩ := same
    unfold PriorPhase.ExactFor at qualified
    rw [arm] at qualified
    exact ⟨support,settled,qualified,active⟩

/-- Same original independent event, same exact native root and signed
report. The per-visit proof retains each original old row authority. It
does not grant native authority to unrelated inner rows. -/
theorem scoped_completed_interior_agrees_with_its_independent_released_event
    {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel} {basis : PriorPhase} {phase : CheckedPhase p.old.state.core}
    {wire : CompletedInteriorWire n}
    (event : TypedInput p gd pos rel)
    (qualified : basis.ExactFor event)
    (original : IsExactReleasedInput event wire.ordinaryOwner phase wire.release.write wire.release.originOrdinal)
    (pin : ExactSelectedRoute event wire.route.route)
    (out : CompletedInterior p gd pos rel basis phase wire) :
    out.output = event.report ∧ out.exactRootRow = event.rootRow ∧
    (⟨wire.ordinaryOwner,event.rawOrdinal,event.rootRow,wire.release.write,wire.release.originOrdinal⟩ :
      CompletedAssociation) ∈ basis.completed ∧
    PhaseOriginAt phase wire.release.write event.rootRow.left wire.release.originOrdinal ∧
    AllRootSafe p.old.state.core pos (p.old.root.demand.arguments.map (fun arg => arg.lower))
      (wire.route.approach.roots.map Checkpoint.which) ∧
    InteriorSourceOrCompletion (p := p) basis.authors out.focused.lexical out.focused.approach.last
      out.focused.approach.finalCard (readPairedIndices wire.route.after) out.focused.suffix.sites.path ∧
    InteriorMeaning (p := p) (visibleReadView basis.authors) out.focused.lexical out.focused.approach.last
      out.focused.approach.finalCard (readPairedIndices wire.route.after) out.focused.suffix.sites.path ∧
    safeAuthorPrefixes (p := p) out.focused.lexical out.focused.suffix.sites.path ∧
    (event.bit = true ↔ ReturnsUpToEquality (graphOf p.old.state.core pos)
      (terminalPair (p := p) out.focused.lexical out.focused.approach.last out.focused.suffix.sites.path).1.index) := by
  have release := completed_interior_keeps_original_release_and_scoped_report out
  have report := release.1.trans (every_accepted_wire_at_the_independent_event_coordinates_reports_the_same_event
    event pin out.focused.exactReport)
  have recorded := original_completed_input_retains_its_independent_active_origin
    event basis wire.ordinaryOwner phase wire.release.write wire.release.originOrdinal qualified original
  obtain ⟨_,_,_,_,_,_,_,_,index,_,_,_,_⟩ := actual_root_pinned_read_iff.mp out.focused.approach.bound
  have loc : out.focused.approach.initial.initialIndices.raw = event.rawOrdinal := by
    change out.focused.approach.initial.initialIndices.raw = _ at index
    change _ = (pos.cells.get wire.route.route.trail.cursor.which).oldOrdinal at index
    exact index.trans ((congrArg (fun i => (pos.cells.get i).oldOrdinal) pin.2.2.1).trans event.physicalRow)
  have real := out.exactRaw
  rw [loc] at real
  have same := Option.some.inj (real.symm.trans event.existingRoot)
  have both := completed_interior_preserves_every_original_model_and_never_retags_an_inner_owner out
  refine ⟨report,same,recorded.2.2.1,recorded.2.2.2,
    requestRootCheckSound _ _ _ _ out.focused.approach.rootChecked,
    both.2.1,both.1,both.2.2.1,?_⟩
  rw [report] at both
  exact both.2.2.2

end Yulang.GeneralDeclarativeI65.I72.Producer479
