import Yulang.GeneralDeclarativeI65I74SelectedReplay447

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


theorem replay_local_input_from_facts {p : Problem}
    {d : GeneralDeclarations.Declaration} (a : RefPositions441.Original p.state p.root d)
    (w : RefPositions441.Wire)
    (loc : p.state.core.origins[w.original]? = some a.original)
    (closedEscape : splitCheck446 p.state.core.current.ordinary a.arg.lower w.escape = true) :
    replayLocalInput p d a.only w = some a := by
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
  have header : selectedHeader p.state.core.current.environment d = true :=
    (selected_header_exact446 p.state.core.current d).mpr ⟨a.noWhere,a.covered,a.checked⟩
  unfold replayLocalInput
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

theorem replay_local_event_from_facts {p : Problem}
    (source : SourceSelection p) (w : RefPositions441.Wire)
    (loc : p.state.core.origins[w.original]? = some source.origin.original.original)
    (escape : splitCheck446 p.state.core.current.ordinary
      source.origin.original.arg.lower w.escape = true)
    (canonicalPlacement : source.origin.event.frame.placement = unusedPlacement403) :
    replayLocalSelected p w = some source.origin := by
  let r := source.origin
  have only : visible p.state.core p.root = [r.decl] :=
    (inputOnly_visible p).symm.trans r.original.only
  have authored :
      (GeneralDeclarativeWitnessDeclaredState357.authoredRegistry p.state.core.current).declarations[r.event.frame.ordinal]? =
        some r.decl := by
    rw [← r.exactDecl]
    exact r.event.frame.authored
  have input := replay_local_input_from_facts r.original w loc escape
  unfold replayLocalSelected
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



theorem ready_local_exact_read {p : Problem}
    (source : SourceSelection p) (w : RefPositions441.Wire)
    (loc : p.state.core.origins[w.original]? = some source.origin.original.original)
    (escape : splitCheck446 p.state.core.current.ordinary
      source.origin.original.arg.lower w.escape = true)
    (canonicalPlacement : source.origin.event.frame.placement = unusedPlacement403) :
    readLocalSource p w = some source := by
  have got := replay_local_event_from_facts source w loc escape canonicalPlacement
  unfold readLocalSource
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



end Yulang.GeneralDeclarativeI65.I72.RetainedSplit446.SelectedReplay447
