import Yulang.GeneralDeclarativeI65I74RetainedPlacement445
import Yulang.GeneralDeclarativeI65I74SplitEscapeFinite446

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RetainedSplit446
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

/-- C445's original input path with only the raw certificate checker changed.
The same actual declaration, header, issuer, constructor modes and input captures are read. -/
def replayInput446 (p : Problem) (d : Declaration)
    (scope : visible p.state.core p.root = [d]) (wire : Wire) :
    Option (Original p.state p.root d) := do
  let core := p.state.core
  let env := core.current.environment
  let raw := core.current.ordinary
  if header : MergedOutput439.checkHeader439 env = true then
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
                        let refined := MergedOutput439.checked_header439 header
                        let actually := ((visible_exact core p.root d).mp
                          (by rw [scope]; exact List.mem_cons_self)).1
                        let safe : ¬RootCycle p.state p.root := by
                          rintro ⟨someArg,mem,cycle⟩
                          rw [asked] at mem
                          cases List.mem_singleton.mp mem
                          exact checked_split_escape_excludes_exact_raw_K2446 verify cycle
                        some {
                          only := scope
                          checked := refined.1.2 d actually
                          covered := refined.2.1 d actually
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


def replaySelected446 (p : Problem) (wire : RefPositions441.Wire) : Option (Replay p) := do
  match scope : visible p.state.core p.root with
  | [d] =>
    let a ← replayInput446 (inputOnly p) d (inputOnly_visible p ▸ scope) wire
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


theorem replay_exact_selected_head446 {p : Problem} {w : RefPositions441.Wire}
    {r : Replay p} (got : replaySelected446 p w = some r) :
    r.event.head = (r.exactDecl.symm ▸ restoreOriginalHead r.original) := by
  unfold replaySelected446 at got
  split at got
  next d scope =>
    cases first : replayInput446 (inputOnly p) d (inputOnly_visible p ▸ scope) w with
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


def readSource446 (p : Problem) (w : RefPositions441.Wire) : Option (SourceSelection p) :=
  match hit : replaySelected446 p w with
  | none => none
  | some source => source.readOwnRefOutput.map (fun own => ⟨source,replay_exact_selected_head446 hit,own⟩)


theorem replay_input_from_split_facts446 {p : Problem}
    {d : GeneralDeclarations.Declaration} (a : RefPositions441.Original p.state p.root d)
    (w : RefPositions441.Wire)
    (header : MergedOutput439.checkHeader439 p.state.core.current.environment = true)
    (loc : p.state.core.origins[w.original]? = some a.original)
    (closedEscape : splitCheck446 p.state.core.current.ordinary a.arg.lower w.escape = true) :
    replayInput446 p d a.only w = some a := by
  have boundary : (d.requirements.isEmpty && p.root.demand.outputs.isEmpty) = true := by
    simp [a.noWhere,a.noOutputs]
  have routes : a.original.issuer = p.root.occurrence ∧ a.original.slot = a.arg.lower ∧
      a.original.slot = a.arg.center ∧ a.original.slot = a.arg.upper :=
    ⟨a.issuer,a.lower,a.center,a.upper⟩
  have hasAtoms : (decide ((PresenceNormalForm.Atom.rowLe (.var a.rowName) (.var a.rowName) :
      PresenceNormalForm.Atom Nat) ∈ p.state.core.current.ordinary.normal.ordinary) &&
    decide ((PresenceNormalForm.Atom.tyLe (.var a.valueName) (.var a.valueName) :
      PresenceNormalForm.Atom Nat) ∈ p.state.core.current.ordinary.normal.ordinary)) = true :=
    Bool.and_eq_true_iff.mpr ⟨decide_eq_true a.rowAtom,decide_eq_true a.valueAtom⟩
  unfold replayInput446
  rw [dite_eq_left header,dite_eq_left boundary]
  split
  · rename_i key rowB valB arg written asked
    have args := (List.cons.inj (asked.symm.trans a.asked)).1
    have hw := (List.cons.inj (written.symm.trans a.written)).1
    change GeneralDeclarationPatterns.Pattern.app key [.var rowB,.var valB] =
      .app a.key [.var a.rowBinder,.var a.valueBinder] at hw
    have parts := GeneralDeclarationPatterns.Pattern.app.inj hw
    have keySame := parts.1
    have row := GeneralDeclarationPatterns.Pattern.var.inj (List.cons.inj parts.2).1
    have value := GeneralDeclarationPatterns.Pattern.var.inj
      (List.cons.inj ((List.cons.inj parts.2).2)).1
    subst key
    subst rowB
    subst valB
    subst arg
    rw [dite_eq_left a.separateBinders,dite_eq_left closedEscape]
    split
    · rename_i no
      rw [loc] at no
      cases no
    · rename_i orig atOrigin
      have id := Option.some.inj (atOrigin.symm.trans loc)
      subst orig
      split
      · rename_i key n k found
        rw [a.read] at found
        have items := CommonRecursiveNominalIntervals.Endpoint.nominal.inj found
        rcases items with ⟨keyEq,argsEq⟩
        have rn := Core.PresenceGeneration.RowTerm.var.inj
          (CommonRecursiveNominalIntervals.Bounds.point.inj
            (Sum.inr.inj (List.cons.inj argsEq).1))
        have vn := Core.PresenceGeneration.TyTerm.var.inj
          (CommonRecursiveNominalIntervals.Endpoint.ordinary.inj
            (CommonRecursiveNominalIntervals.Bounds.point.inj
              (Sum.inl.inj (List.cons.inj ((List.cons.inj argsEq).2)).1)))
        subst key
        subst n
        subst k
        rw [dite_eq_left (show a.key = a.key ∧ _ from ⟨rfl,routes⟩)]
        rw [read_use_reconstructs_exact_placement445 a.use]
        simp only [bind,Option.bind]
        split
        · rename_i ps modeEq
          rw [a.fromBody] at modeEq
          have layoutEq := Mode.declared.inj modeEq
          subst ps
          rw [dite_eq_left (show RefPositions441.layout = RefPositions441.layout ∧ _ from ⟨rfl,a.table⟩),
               dite_eq_left hasAtoms]
        · rename_i wrong
          exact (wrong _ a.fromBody).elim
      · rename_i wrong
        exact (wrong _ _ _ a.read).elim
  · rename_i wrong
    exact (wrong _ _ _ _ a.written a.asked).elim


private theorem exact_actual_frame_at_named_source446
    {s : GeneralDeclarativeI65.State} {q : I72.Request}
    (first last : AuthoredBodyFrame393 s q)
    (ordinal : first.ordinal = last.ordinal) (decl : first.decl = last.decl)
    (place : first.placement = last.placement) (capture : first.input = last.input) :
    first = last := by
  cases first
  cases last
  simp_all

private theorem dependent_transport_keeps_data446 {A : Type} {P : A → Type}
    {a b : A} (same : a = b) (obj : P a) : HEq (same ▸ obj) obj := by
  cases same
  rfl

private theorem same_replay_at_event446 {p : Problem} (a b : Replay p)
    (decl : a.decl = b.decl) (input : HEq a.original b.original)
    (event : a.event = b.event) : a = b := by
  cases a
  cases b
  dsimp at *
  subst_vars
  rfl

private theorem same_exact_event446 {s : I72.State} {q : I72.Request} (a b : Event s q)
    (frame : a.frame = b.frame) (head : HEq a.head b.head)
    (all : ∀ i, HEq (a.outputs i) (b.outputs i)) : a = b := by
  cases a
  cases b
  dsimp at *
  subst_vars
  congr
  funext i
  exact eq_of_heq (all i)

theorem replay_event_from_split_facts446 {p : Problem}
    (source : SourceSelection p) (w : RefPositions441.Wire)
    (header : MergedOutput439.checkHeader439 p.state.core.current.environment = true)
    (loc : p.state.core.origins[w.original]? = some source.origin.original.original)
    (escape : splitCheck446 p.state.core.current.ordinary
      source.origin.original.arg.lower w.escape = true)
    (canonicalPlacement : source.origin.event.frame.placement = unusedPlacement403) :
    replaySelected446 p w = some source.origin := by
  let r := source.origin
  have only : visible p.state.core p.root = [r.decl] :=
    (inputOnly_visible p).symm.trans r.original.only
  have authored :
      (GeneralDeclarativeWitnessDeclaredState357.authoredRegistry p.state.core.current).declarations[r.event.frame.ordinal]? =
        some r.decl := by
    rw [← r.exactDecl]
    exact r.event.frame.authored
  have input := replay_input_from_split_facts446 r.original w header loc escape
  unfold replaySelected446
  split
  · rename_i d singleton
    have sameDecl := (List.cons.inj (singleton.symm.trans only)).1
    subst d
    rw [input]
    simp only [bind,Option.bind]
    split
    · rename_i miss
      rw [r.exactOrdinal] at miss
      cases miss
    · rename_i idx found
      have same := Option.some.inj (found.symm.trans r.exactOrdinal)
      subst idx
      rw [dite_eq_left authored,dite_eq_left r.onlyOutput]
      let freshFrame :=
        frameAtSource395 (originalCandidate r.original).inScope r.event.frame.ordinal authored
          unusedPlacement403 (preoutputInputOfHead399 (originalCandidate r.original).head
            (fun _ => emptyCapture403))
      have frames : freshFrame = r.event.frame := by
        refine exact_actual_frame_at_named_source446 _ _ rfl r.exactDecl.symm
          canonicalPlacement.symm ?_
        exact (restored_input_is_exact442 r.original).trans r.exactInput.symm
      let out : NamedMixedOutput401 p.state.b6 freshFrame r.i0 :=
        frames.symm ▸ r.event.outputs r.i0
      have read := read_output_reconstructs_actual_typed_body445 r.original.checked out
      change (readNamedOutput442 p.state freshFrame r.original.checked r.i0).bind _ = some r
      rw [read]
      simp only [Option.bind]
      apply congrArg some
      apply same_replay_at_event446
      · rfl
      · rfl
      · apply same_exact_event446
        · exact frames
        · have native : HEq
              (r.exactDecl.symm ▸ restoreOriginalHead r.original) (restoreOriginalHead r.original) :=
            dependent_transport_keeps_data446
              (P := fun d => SourceHead p.state.core p.root d) r.exactDecl.symm _
          exact native.symm.trans (heq_of_eq source.head.symm)
        · intro i
          have same : i = r.i0 := Fin.ext (by
            have lt := Nat.lt_of_lt_of_eq i.isLt r.onlyOutput
            change i.val = 0
            omega)
          subst i
          change HEq out (r.event.outputs r.i0)
          exact dependent_transport_keeps_data446
            (P := fun f => NamedMixedOutput401 p.state.b6 f r.i0) frames.symm _
  · rename_i notOne
    exact (notOne _ only).elim



theorem ready_split_exact_read446 {p : Problem}
    (source : SourceSelection p) (w : RefPositions441.Wire)
    (header : MergedOutput439.checkHeader439 p.state.core.current.environment = true)
    (loc : p.state.core.origins[w.original]? = some source.origin.original.original)
    (escape : splitCheck446 p.state.core.current.ordinary
      source.origin.original.arg.lower w.escape = true)
    (canonicalPlacement : source.origin.event.frame.placement = unusedPlacement403) :
    readSource446 p w = some source := by
  have got := replay_event_from_split_facts446 source w header loc escape canonicalPlacement
  unfold readSource446
  split
  · rename_i no
    rw [got] at no
    cases no
  · rename_i hit read
    have same := Option.some.inj (read.symm.trans got)
    subst hit
    rw [readOwn_reconstructs_actual_source_output445 source.origin source.own]
    cases source
    rfl


end Yulang.GeneralDeclarativeI65.I72.RetainedSplit446
