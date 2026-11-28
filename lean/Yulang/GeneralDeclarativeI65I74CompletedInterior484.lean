import Yulang.GeneralDeclarativeI65I74PairedVisibleSupport484
import Yulang.GeneralDeclarativeI65I74RootedInteriorReport483
import Yulang.GeneralDeclarativeI65I74TypedCompletedFocus482
import Yulang.GeneralDeclarativeI65I74SignedInteriorTerminal483
import Yulang.GeneralDeclarativeI65I74AuthoredInteriorSafety483

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open ObservationAlternatives473 (Positions)
open Producer479 (PriorPhase ReleasedIssueData CompletedAssociation readBoundReleasedIssue)
open NativeProducer465 (CheckedPhase PhaseOriginAt)
open InputCoordinates475 (rawAt SamePhaseInputObservation478)
open GeneralDeclarativeWitnessOrigins350 (Attached attach)
open GeneralDeclarativeHead320 (Equation)

structure CompletedInteriorWire (n : Nat) where
  route : RootedInteriorWire n
  ordinaryOwner : Nat
  producedOrdinal : Nat
  release : ReleasedIssueData

structure CompletedInterior {n : Nat} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n)) (basis : PriorPhase)
    (phase : CheckedPhase p.old.state.core) (w : CompletedInteriorWire n) where
  attached : Attached (rawAt p) basis.authors
  focused : RootedInteriorReceipt p gd pos rel (visibleBasis basis) w.route
  exactRootRow : Equation
  exactRaw : (rawAt p).equations[focused.approach.initial.initialIndices.raw]? = some exactRootRow
  exactOrigin : (visibleWithAuthority basis.authors)[focused.approach.initial.initialIndices.author]? =
    some (.completed w.producedOrdinal w.ordinaryOwner,exactRootRow)
  output : SamePhaseInputObservation478
  releasedChecked : readBoundReleasedIssue p gd pos rel basis phase w.ordinaryOwner w.route.route w.release = some output

def readCompletedInterior {n : Nat} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n)) (basis : PriorPhase)
    (phase : CheckedPhase p.old.state.core) (w : CompletedInteriorWire n) :
    Option (CompletedInterior p gd pos rel basis phase w) := do
  let attached ← attach (rawAt p) basis.authors
  let focused ← readRootedInterior p gd pos rel (visibleBasis basis) w.route
  let row ← collectedForInterior ((rawAt p).equations[focused.approach.initial.initialIndices.raw]?)
  if strong : (visibleWithAuthority basis.authors)[focused.approach.initial.initialIndices.author]? =
      some (.completed w.producedOrdinal w.ordinaryOwner,row.val) then
    let verified ← collectedForInterior (readBoundReleasedIssue p gd pos rel basis phase w.ordinaryOwner w.route.route w.release)
    some ⟨attached,focused,row.val,row.property,strong,verified.val,verified.property⟩
  else none

theorem completed_interior_keeps_original_release_and_scoped_report
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {basis : PriorPhase} {phase : CheckedPhase p.old.state.core}
    {w : CompletedInteriorWire n} (accepted : CompletedInterior p gd pos rel basis phase w) :
    accepted.output = accepted.focused.report ∧
    basis.authors.produced[w.producedOrdinal]? = some (accepted.exactRootRow,w.ordinaryOwner) ∧
    w.ordinaryOwner ∈ basis.authors.released ∧
    (⟨w.ordinaryOwner,accepted.focused.approach.initial.initialIndices.raw,accepted.exactRootRow,
      w.release.write,w.release.originOrdinal⟩ : CompletedAssociation) ∈ basis.completed ∧
    PhaseOriginAt phase w.release.write accepted.exactRootRow.left w.release.originOrdinal := by
  obtain ⟨_,_,_,_,_,_,_,_,rawIndex,_,_,_,_⟩ := actual_root_pinned_read_iff.mp accepted.focused.approach.bound
  obtain ⟨releaseRow,exactAt,association,released,run⟩ :=
    Producer479.exact_output_association_and_current_release_replay479.mp accepted.releasedChecked
  have sameRun := Option.some.inj (run.symm.trans accepted.focused.exactReport)
  change accepted.focused.approach.initial.initialIndices.raw =
    (pos.cells.get w.route.route.trail.cursor.which).oldOrdinal at rawIndex
  have picked := accepted.exactRaw
  rw [rawIndex] at picked
  have sameEq : releaseRow = accepted.exactRootRow := Option.some.inj (exactAt.symm.trans picked)
  have storedInView : (visibleReadView basis.authors).authored[accepted.focused.approach.initial.initialIndices.author]? =
      some accepted.exactRootRow := by
    rw [←visibleWithAuthority_erases_to_exact_input_view,List.getElem?_map,accepted.exactOrigin]
    rfl
  obtain ⟨authority,label,valid⟩ := each_projected_view_slot_has_original_ordinal_authority _ _ _ storedInView
  rw [accepted.exactOrigin] at label
  have exactLabel := congrArg Prod.fst (Option.some.inj label)
  change ReadRowAuthority.completed w.producedOrdinal w.ordinaryOwner = authority at exactLabel
  subst authority
  rw [sameEq] at association released
  exact ⟨sameRun,valid.1,valid.2,rawIndex.symm ▸ association,released⟩

open ObservationAlternatives473 (oldPosition graphOf)
open LiteralVisits473 (read_checkpoint_guards)
open CommonRoleGraphBisimulation (ObservationallyEqual)
open QuotientObservation471 (ReturnsUpToEquality)

theorem completed_interior_preserves_every_original_model_and_never_retags_an_inner_owner
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {basis : PriorPhase} {phase : CheckedPhase p.old.state.core}
    {w : CompletedInteriorWire n} (accepted : CompletedInterior p gd pos rel basis phase w) :
    InteriorMeaning (p := p) (visibleReadView basis.authors) accepted.focused.lexical accepted.focused.approach.last
      accepted.focused.approach.finalCard (readPairedIndices w.route.after) accepted.focused.suffix.sites.path ∧
    InteriorSourceOrCompletion (p := p) basis.authors accepted.focused.lexical accepted.focused.approach.last
      accepted.focused.approach.finalCard (readPairedIndices w.route.after) accepted.focused.suffix.sites.path ∧
    safeAuthorPrefixes (p := p) accepted.focused.lexical accepted.focused.suffix.sites.path ∧
    (accepted.output.outcome.2.2.2 = true ↔
      ReturnsUpToEquality (graphOf p.old.state.core pos)
        (terminalPair (p := p) accepted.focused.lexical accepted.focused.approach.last accepted.focused.suffix.sites.path).1.index) := by
  let out := accepted.focused
  obtain ⟨walk,source⟩ := paired_visible_path_retains_original_completed_support_and_same_models
    accepted.attached out.suffix.sites.actual
  have check := read_checkpoint_guards out.approach.conclusion.checkedSign
  have ambientIndex := (Producer479.reified_hop_keeps_the_same_old_place479 out.approach.lastRead).1
  have same : ObservationallyEqual (graphOf p.old.state.core pos) out.lexical.index out.approach.last.index := by
    rw [out.anchorIndex,←ambientIndex]
    exact fun d => (out.approach.conclusion.agrees d).symm
  have sign := signed_interior_terminal_is_the_same_physical_site_and_same_quotient_sign check.1.2.1 same out.suffix
  have root := completed_interior_keeps_original_release_and_scoped_report accepted
  rw [root.1,out.sameBit]
  exact ⟨walk,source,every_nonterminal_original_author_site_in_the_rooted_suffix_is_safe out,sign.2⟩


end Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank
