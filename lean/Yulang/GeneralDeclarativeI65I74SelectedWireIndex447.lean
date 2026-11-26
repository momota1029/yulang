import Yulang.GeneralDeclarativeI65I74SelectedExact447

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RetainedSplit446.SelectedReplay447
open Yulang.GeneralDeclarativeI65
open GeneralDeclarations (Declaration)
open GeneralDeclarativeWitnessConstructorModes357 (Mode readUse)
open Checker408 (Problem Result)
open PresenceNormalForm (Atom)
open RefPositions441 (Wire Original layout)
open MixedFixed442
open RetainedFull445
open SplitEscape446

theorem successful_input_exact_origin447 {p : Problem} {d : Declaration}
    {scope : visible p.state.core p.root = [d]} {w : Wire} {a : Original p.state p.root d}
    (got : replayLocalInput p d scope w = some a) :
    p.state.core.origins[w.original]? = some a.original ∧
      splitCheck446 p.state.core.current.ordinary a.arg.lower w.escape = true := by
  unfold replayLocalInput at got
  repeat first
    | cases got
    | simp only [Bind.bind,Option.bind] at got
    | split at got
  all_goals first | contradiction | exact ⟨by assumption,by assumption⟩

theorem successful_event_exact_origin447 {p : Problem} {w : Wire}
    {r : Replay p} (got : replayLocalSelected p w = some r) :
    p.state.core.origins[w.original]? = some r.original.original ∧
      splitCheck446 p.state.core.current.ordinary r.original.arg.lower w.escape = true := by
  unfold replayLocalSelected at got
  split at got
  next d scope =>
    cases first : replayLocalInput (inputOnly p) d (inputOnly_visible p ▸ scope) w with
    | none => simp [first,Bind.bind,Option.bind] at got
    | some a =>
      simp only [first,Bind.bind,Option.bind] at got
      split at got
      · cases got
      · split at got
        · split at got
          · split at got
            · cases got
            · cases Option.some.inj got
              exact successful_input_exact_origin447 first
          · cases got
        · cases got
  all_goals cases got

theorem successful_source_exact_origin447 {p : Problem} {w : Wire}
    {a : SourceSelection p} (got : readLocalSource p w = some a) :
    p.state.core.origins[w.original]? = some a.origin.original.original ∧
      splitCheck446 p.state.core.current.ordinary a.origin.original.arg.lower w.escape = true := by
  unfold readLocalSource at got
  split at got
  · cases got
  · rename_i r replay
    cases own : r.readOwnRefOutput with
    | none => simp [own] at got
    | some data =>
      simp only [own,Option.map_some] at got
      cases Option.some.inj got
      exact successful_event_exact_origin447 replay

theorem accepted_wire_checks_exact_origin_and_report447 {p : FullProblem} {r : Result}
    {w : Wire} (yes : check_full447 p r (.localSplitOutput w) = true) :
    ∃ a : LocalSelection p.state p.root,
      p.state.base.core.origins[w.original]? = some a.source.origin.original.original ∧
      splitCheck446 p.state.base.core.current.ordinary a.source.origin.original.arg.lower w.escape = true ∧
      r = a.report := by
  obtain ⟨a,replayed,report⟩ := accepted_wire_reflects_same_local_source447 yes
  have actual := successful_source_exact_origin447 replayed
  exact ⟨a,actual.1,actual.2,report⟩


end Yulang.GeneralDeclarativeI65.I72.RetainedSplit446.SelectedReplay447
