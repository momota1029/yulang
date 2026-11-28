import Yulang.GeneralDeclarativeI65I74SignedInteriorTerminal483
import Yulang.GeneralDeclarativeI65I74NamedTerminalRoute482

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank
open RetainedFull445 (FullProblem)
open Producer479 (Site PriorPhase RouteWire readRoute siteAt)
open PreparedDeclarations463 (CheckedTable)
open LiteralVisits473 (Checkpoint read_checkpoint_guards)
open ObservationAlternatives473 (Positions oldPosition graphOf)
open GeneralDeclarativeOrigins321 (Supported)
open InputCoordinates475 (rawAt SamePhaseInputObservation478)
open TypedRootSafety482 (AllRootSafe requestRootCheckSound)
open CommonRoleGraphBisimulation (ObservationallyEqual)
open QuotientObservation471 (ReturnsUpToEquality)

structure RootedInteriorWire (n : Nat) where
  approach : NamedTerminalWire n
  after : List (Fin n × Checkpoint n × LiteralVisits473.StepWire)

def RootedInteriorWire.continuation (w : RootedInteriorWire n) : SignedInteriorWire n :=
  ⟨w.approach.terminal,w.after⟩

def RootedInteriorWire.route (w : RootedInteriorWire n) : RouteWire n :=
  ⟨w.approach.argument,w.approach.declarationOrdinal,
    ⟨w.approach.cursor,w.approach.route.trail.tail ++ w.continuation.ambient.tail⟩⟩

structure RootedInteriorReceipt {n : Nat} (p : FullProblem)
    (gd : CheckedTable p.old.state.core.current) (pos : Positions n)
    (rel : List (Fin n × Fin n)) (basis : PriorPhase) (w : RootedInteriorWire n) where
  approach : NamedTerminalReceipt p gd pos rel basis w.approach
  openHere : approach.conclusion.sign = false
  lexical : Site p.old.state.core pos
  anchored : siteAt (s := p.old.state.core) (pos := pos)
    approach.conclusion.lexical approach.last.pattern approach.last.query = some lexical
  anchorIndex : lexical.index = approach.conclusion.lexical
  suffix : SignedInteriorPath (p := p) basis.authors lexical approach.last approach.finalCard rel w.continuation
  report : SamePhaseInputObservation478
  exactReport : readRoute p gd pos rel w.route = some report
  sameTerminal : report.outcome.2.2.1 = oldPosition pos suffix.terminal.index
  sameBit : report.outcome.2.2.2 = suffix.bit

/-- A full original route and its paired typed continuation keep exact
separate evidence. The existing all-argument guard is read in the named
approach. No change to the canonical dispatcher or older report schema. -/
def readRootedInterior {n : Nat} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n)) (basis : PriorPhase) (w : RootedInteriorWire n) :
    Option (RootedInteriorReceipt p gd pos rel basis w) := do
  let prior ← readNamedTerminalRoute p gd pos rel basis w.approach
  if safe : prior.conclusion.sign = false then
    let anchor ← collectedForInterior (siteAt (s := p.old.state.core) (pos := pos)
      prior.conclusion.lexical prior.last.pattern prior.last.query)
    if exactIndex : anchor.val.index = prior.conclusion.lexical then
      let suffix ← readSignedInteriorPath (p := p) basis.authors anchor.val prior.last prior.finalCard rel w.continuation
      let report ← collectedForInterior (readRoute p gd pos rel w.route)
      if same : report.val.outcome.2.2.1 = oldPosition pos suffix.terminal.index ∧
          report.val.outcome.2.2.2 = suffix.bit then
        some ⟨prior,safe,anchor.val,anchor.property,exactIndex,suffix,report.val,report.property,same.1,same.2⟩
      else none
    else none
  else none

theorem rooted_interior_keeps_the_original_full_report_and_old_author_typing
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {basis : PriorPhase} {w : RootedInteriorWire n}
    (out : RootedInteriorReceipt p gd pos rel basis w)
    {done : Nat → Prop} {support : Supported (rawAt p) done}
    (authored : ∀ row ∈ basis.authors.authored, support.derivesFrom row .source) :
    AllRootSafe p.old.state.core pos (p.old.root.demand.arguments.map (fun a => a.lower))
      (w.approach.roots.map Checkpoint.which) ∧
    readRoute p gd pos rel w.route = some out.report ∧
    InteriorMeaning (p := p) basis.authors out.lexical out.approach.last out.approach.finalCard
      (readPairedIndices w.after) out.suffix.sites.path ∧
    (out.report.outcome.2.2.2 = true ↔ ReturnsUpToEquality (graphOf p.old.state.core pos)
      (terminalPair (p := p) out.lexical out.approach.last out.suffix.sites.path).1.index) := by
  obtain ⟨attached,_,_,_,_,_,_,_,_,_,_,_,_⟩ := actual_root_pinned_read_iff.mp out.approach.bound
  have oldCheckpoint := read_checkpoint_guards out.approach.conclusion.checkedSign
  have ambientIndex := (Producer479.reified_hop_keeps_the_same_old_place479 out.approach.lastRead).1
  have same : ObservationallyEqual (graphOf p.old.state.core pos) out.lexical.index out.approach.last.index := by
    rw [out.anchorIndex,←ambientIndex]
    exact fun d => (out.approach.conclusion.agrees d).symm
  have mode := signed_interior_terminal_is_the_same_physical_site_and_same_quotient_sign
    oldCheckpoint.1.2.1 same out.suffix
  exact ⟨requestRootCheckSound _ _ _ _ out.approach.rootChecked,out.exactReport,
    paired_path_retains_the_independent_source_typing_at_each_read_origin attached authored out.suffix.sites.actual,
    out.sameBit.symm ▸ mode.2⟩

end Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank
