import Yulang.GeneralDeclarativeI65I74RetainedSplitEntry446
import Yulang.GeneralDeclarativeI65I74RetainedLocalHeader446

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RetainedSplit446.SelectedReplay447
open Yulang.GeneralDeclarativeI65
open GeneralDeclarations (Declaration)
open GeneralDeclarativeWitnessConstructorModes357 (Mode readUse)
open GeneralDeclarativeWitnessProblem349 (splitAnd)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open Checker408 (Problem)
open PresenceNormalForm (Atom)
open RefPositions441 (Wire Original layout)
open MixedFixed442
open RetainedFull445
open SplitEscape446
open RetainedSplit446.LocalHeader (selectedHeader selected_header_exact446)

/-- The selected declaration is checked locally. This uses the original issuer,
constructor modes and captures, and the separate raw cycle certificate. -/
def replayLocalInput (p : Problem) (d : Declaration)
    (scope : visible p.state.core p.root = [d]) (wire : Wire) :
    Option (Original p.state p.root d) := do
  let core := p.state.core
  let env := core.current.environment
  let raw := core.current.ordinary
  if header : selectedHeader env d = true then
    if boundary : (d.requirements.isEmpty && p.root.demand.outputs.isEmpty) = true then
      match written : d.head, asked : p.root.demand.arguments with
      | [.app key [.var rowBinder,.var valueBinder]],[arg] =>
        if separate : rowBinder ≠ valueBinder then
          if verify : splitCheck446 raw arg.lower wire.escape = true then
            match atOrigin : core.origins[wire.original]? with
            | none => none
            | some original =>
              match read : original.endpoint with
              | .nominal observed [.inr (.point (.var r)),.inl (.point (.ordinary (.var v)))] =>
                if routes : observed = key ∧ original.issuer = p.root.occurrence ∧
                    original.slot = arg.lower ∧ original.slot = arg.center ∧ original.slot = arg.upper then
                  let use ← readUse env key 2
                  match source : use.mode with
                  | .declared params =>
                    if exact : params = layout ∧ core.modes[key]? = some layout then
                      if atoms : decide ((Atom.rowLe (.var r) (.var r) : Atom Nat) ∈ raw.normal.ordinary) &&
                          decide ((Atom.tyLe (.var v) (.var v) : Atom Nat) ∈ raw.normal.ordinary) then
                        let refined := (selected_header_exact446 core.current d).mp header
                        let safe : ¬RootCycle p.state p.root := by
                          rintro ⟨someArg,mem,cycle⟩
                          rw [asked] at mem
                          cases List.mem_singleton.mp mem
                          exact checked_split_escape_excludes_exact_raw_K2446 verify cycle
                        some {
                          only := scope
                          checked := refined.2.2
                          covered := refined.2.1
                          noWhere := List.isEmpty_iff.mp (splitAnd boundary).1
                          noOutputs := List.isEmpty_iff.mp (splitAnd boundary).2
                          arg := arg
                          asked := asked
                          key := key
                          rowBinder := rowBinder
                          valueBinder := valueBinder
                          separateBinders := separate
                          written := written
                          original := original
                          authored := List.mem_of_getElem? atOrigin
                          issuer := routes.2.1
                          lower := routes.2.2.1
                          center := routes.2.2.2.1
                          upper := routes.2.2.2.2
                          rowName := r
                          valueName := v
                          read := by rw [read,routes.1]; rfl
                          use := use
                          fromBody := by rw [source,exact.1]
                          table := exact.2
                          rowAtom := of_decide_eq_true (splitAnd atoms).1
                          valueAtom := of_decide_eq_true (splitAnd atoms).2
                          safe := safe }
                      else none
                    else none
                  | _ => none
                else none
              | _ => none
          else none
        else none
      | _,_ => none
    else none
  else none


def replayLocalSelected (p : Problem) (wire : RefPositions441.Wire) : Option (Replay p) := do
  match scope : visible p.state.core p.root with
  | [d] =>
    let a ← replayLocalInput (inputOnly p) d (inputOnly_visible p ▸ scope) wire
    let c := originalCandidate a
    let reg := authoredRegistry p.state.core.current
    match h : unfilterOrdinal395 (fun row : Declaration => row.role == p.root.demand.role)
        reg.declarations 0 with
    | none => none
    | some ordinal =>
      if authored : reg.declarations[ordinal]? = some d then
        if only : p.root.demand.outputs.length = 1 then
          let f := frameAtSource395 c.inScope ordinal authored unusedPlacement403
            (preoutputInputOfHead399 c.head (fun _ => emptyCapture403))
          let i : Fin p.root.demand.outputs.length := ⟨0,by rw [only]; decide⟩
          let output ← readNamedOutput442 p.state f a.checked i
          let e : Event p.state p.root := ⟨f,c.head,fun j =>
            (show i = j from Fin.ext (by
              have dj : j.val < 1 := Nat.lt_of_lt_of_eq j.isLt only
              change 0 = j.val
              omega)) ▸ output⟩
          some ⟨d,a,e,rfl,h,restored_input_is_exact442 a,
            by simp [e,Event.kids,frameWhereKids400,f,frameAtSource395,AuthoredBodyFrame393.clauses,
              a.noWhere,children],only⟩
        else none
      else none
  | _ => none


theorem replay_local_exact_selected_head {p : Problem} {w : RefPositions441.Wire}
    {r : Replay p} (got : replayLocalSelected p w = some r) :
    r.event.head = (r.exactDecl.symm ▸ restoreOriginalHead r.original) := by
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
              rfl
          · cases got
        · cases got
  all_goals cases got


def readLocalSource (p : Problem) (w : RefPositions441.Wire) : Option (SourceSelection p) :=
  match hit : replayLocalSelected p w with
  | none => none
  | some source => source.readOwnRefOutput.map (fun own => ⟨source,replay_local_exact_selected_head hit,own⟩)


end Yulang.GeneralDeclarativeI65.I72.RetainedSplit446.SelectedReplay447
