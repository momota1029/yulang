import Yulang.GeneralDeclarativeI65I74ExactScopedInterior483
import Yulang.GeneralDeclarativeI65I74SignedInteriorReplay483
import Yulang.GeneralDeclarativeI65I74ProducerSingleVisible479
import Yulang.GeneralDeclarativeI65I74ExactIndependentSourceEvent484

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open ObservationAlternatives473 (Positions oldPosition)
open Producer479 (Site siteAt PriorPhase TypedInput ExactSelectedRoute readTrail readRoute)

private theorem exact_option_pair {T : Type} {p : Option T} {r : T} (one : p = some r) :
    collectedForInterior p = some ⟨r,one⟩ := by
  subst p
  rfl

/-- A scoped converse: if the old authenticated named approach is separately
replayed and a genuinely typed finite pair path is supplied, the independent
event fixes the accepted external report. The existence of those separate
typed interior components is intentionally not inferred from the event. -/
theorem qualified_components_reify_the_same_independent_scoped_event
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel} {basis : PriorPhase} {w : RootedInteriorWire n}
    (event : TypedInput p gd pos rel)
    (selected : ExactSelectedRoute event w.route)
    {observed : InputCoordinates475.SamePhaseInputObservation478}
    (readGeometry : readRoute p gd pos rel w.route = some observed)
    {pre : NamedTerminalReceipt p gd pos rel basis w.approach}
    (approach : readNamedTerminalRoute p gd pos rel basis w.approach = some pre)
    (atCut : pre.conclusion.sign = false)
    {lex : Site p.old.state.core pos}
    (found : siteAt (s := p.old.state.core) (pos := pos) pre.conclusion.lexical
      pre.last.pattern pre.last.query = some lex)
    (bound : lex.index = pre.conclusion.lexical)
    {path terminal bit}
    (components : InteriorComponentReads (p := p) basis.authors lex pre.last pre.finalCard
      (readPairedIndices w.after) path)
    (signed : readTrail rel pre.last w.continuation.ambient = some (terminal,bit))
    (finish : terminal = event.final) (sameBit : bit = event.bit) :
    checkScopedInterior483 p gd pos rel basis w event.report = true := by
  have g := (Producer479.every_accepted_wire_at_the_independent_event_coordinates_reports_the_same_event
    event selected readGeometry) ▸ readGeometry
  have exactPath : InteriorComponentReads (p := p) basis.authors lex pre.last pre.finalCard
      (readPairedIndices w.continuation.moves) path := components
  obtain ⟨trace,ran,_,out,judge⟩ :=
    validated_local_components_and_old_sign_replay_the_exact_signed_interior exactPath signed
  apply exact_scoped_interior_check_replays_the_same_rooted_read.mpr
  have exactScope : event.report.outcome.2.2.1 = oldPosition pos trace.terminal.index ∧
      event.report.outcome.2.2.2 = trace.bit := by
    rw [out,judge,finish,sameBit]
    exact ⟨rfl,rfl⟩
  let got : RootedInteriorReceipt p gd pos rel basis w :=
    ⟨pre,atCut,lex,found,bound,trace,event.report,g,exactScope.1,exactScope.2⟩
  refine ⟨got,?_,rfl⟩
  simp [readRootedInterior,approach,atCut,exact_option_pair found,bound,ran,exact_option_pair g,exactScope,
    got,bind,Option.bind]

end Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank
