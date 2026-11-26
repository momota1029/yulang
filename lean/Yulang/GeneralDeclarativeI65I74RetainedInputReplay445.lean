import Yulang.GeneralDeclarativeI65I74WriterReplay445

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RetainedFull445
open Yulang.GeneralDeclarativeI65
open GeneralDeclarativeWitnessConstructorModes357 (Environment Use SourceMode Layout Mode readUse)
open GeneralDeclarativeWitnessModeCoverage357 (available)
open GeneralSourceMetadataRows291 (constructors)
open Checker408 (Problem)
open MixedFixed442

theorem read_use_reconstructs_exact_placement445 {e : Environment} {name arity}
    (u : Use e name arity) : readUse e name arity = some u := by
  obtain ⟨mode,seen,same⟩ := available u.sourced
  have facts : u.declared.name = name ∧ u.current.name = name ∧
        u.current.parameters = u.declared.parameters ∧ u.declared.parameters.length = arity ∧
        Layout u.declared mode.val :=
    ⟨u.declaredName,u.currentName,u.sameLayout,u.exactArity,same.symm ▸ u.kinded⟩
  unfold readUse
  rw [dite_eq_left u.noDefault]
  split
  · rename_i a b ha hb
    have ea := Option.some.inj (ha.symm.trans u.actual)
    have eb := Option.some.inj (hb.symm.trans u.snapshot)
    subst a
    subst b
    rw [seen]
    simp only [bind,Option.bind,dite_eq_left facts]
    cases u
    dsimp at same ⊢
    cases same
    rfl
  · rename_i bad
    exact False.elim ((bad _ _ u.actual) u.snapshot)

theorem read_output_reconstructs_actual_typed_body445 {s : I72.State} {q : I72.Request}
    {f : AuthoredBodyFrame393 s.core q} {i : Fin q.demand.outputs.length}
    (checked : GeneralDeclarations.DeclarationChecked
      (GeneralDeclarativeWitnessDeclaredState357.authoredRegistry s.core.current).constructors
      (GeneralDeclarativeWitnessDeclaredState357.authoredRegistry s.core.current).roles f.decl)
    (o : NamedMixedOutput401 s.b6 f i) :
    readNamedOutput442 s f checked i = some o := by
  obtain ⟨body,supplied,plan,inAtlas,rhs,formed⟩ := o
  have atBody := (GeneralDictionaryAssociatedProvenance.lookup_exact _ _
    checked.identified.2.2.1 _ _).mpr supplied
  unfold readNamedOutput442
  split
  · rw [atBody] at *
    contradiction
  · rename_i found h
    rw [atBody] at h
    cases Option.some.inj h
    split
    · rw [inAtlas] at *
      contradiction
    · rename_i got hg
      rw [inAtlas] at hg
      cases Option.some.inj hg
      split
      · rw [formed] at *
        contradiction
      · rename_i tree ht
        rw [formed] at ht
        cases Option.some.inj ht
        rfl

theorem replay_original_input_from_finite_facts445 {p : Problem}
    {d : GeneralDeclarations.Declaration} (a : RefPositions441.Original p.state p.root d)
    (w : RefPositions441.Wire)
    (header : MergedOutput439.checkHeader439 p.state.core.current.environment = true)
    (loc : p.state.core.origins[w.original]? = some a.original)
    (closedEscape : List410.checkExactEscape p.state.core.current.ordinary a.arg.lower w.escape = true) :
    RefPositions441.replay441 p d a.only w = some a := by
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
  unfold RefPositions441.replay441
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


private theorem exact_actual_frame_at_named_source445
    {s : GeneralDeclarativeI65.State} {q : I72.Request}
    (first last : AuthoredBodyFrame393 s q)
    (ordinal : first.ordinal = last.ordinal) (decl : first.decl = last.decl)
    (place : first.placement = last.placement) (capture : first.input = last.input) :
    first = last := by
  cases first
  cases last
  simp_all

private theorem dependent_transport_keeps_data445 {A : Type} {P : A → Type}
    {a b : A} (same : a = b) (obj : P a) : HEq (same ▸ obj) obj := by
  cases same
  rfl

private theorem same_replay_at_event445 {p : Problem} (a b : Replay p)
    (decl : a.decl = b.decl) (input : HEq a.original b.original)
    (event : a.event = b.event) : a = b := by
  cases a
  cases b
  dsimp at *
  subst_vars
  rfl

private theorem same_exact_event445 {s : I72.State} {q : I72.Request} (a b : Event s q)
    (frame : a.frame = b.frame) (head : HEq a.head b.head)
    (all : ∀ i, HEq (a.outputs i) (b.outputs i)) : a = b := by
  cases a
  cases b
  dsimp at *
  subst_vars
  congr
  funext i
  exact eq_of_heq (all i)

theorem replay_selected_frame_from_finite_facts445 {p : Problem}
    (source : SourceSelection p) (w : RefPositions441.Wire)
    (header : MergedOutput439.checkHeader439 p.state.core.current.environment = true)
    (loc : p.state.core.origins[w.original]? = some source.origin.original.original)
    (escape : List410.checkExactEscape p.state.core.current.ordinary
      source.origin.original.arg.lower w.escape = true)
    (canonicalPlacement : source.origin.event.frame.placement = unusedPlacement403) :
    replay442 p w = some source.origin := by
  let r := source.origin
  have only : visible p.state.core p.root = [r.decl] :=
    (inputOnly_visible p).symm.trans r.original.only
  have authored :
      (GeneralDeclarativeWitnessDeclaredState357.authoredRegistry p.state.core.current).declarations[r.event.frame.ordinal]? =
        some r.decl := by
    rw [← r.exactDecl]
    exact r.event.frame.authored
  have input := replay_original_input_from_finite_facts445 r.original w header loc escape
  unfold replay442
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
        refine exact_actual_frame_at_named_source445 _ _ rfl r.exactDecl.symm
          canonicalPlacement.symm ?_
        exact (restored_input_is_exact442 r.original).trans r.exactInput.symm
      let out : NamedMixedOutput401 p.state.b6 freshFrame r.i0 :=
        frames.symm ▸ r.event.outputs r.i0
      have read := read_output_reconstructs_actual_typed_body445 r.original.checked out
      change (readNamedOutput442 p.state freshFrame r.original.checked r.i0).bind _ = some r
      rw [read]
      simp only [Option.bind]
      apply congrArg some
      apply same_replay_at_event445
      · rfl
      · rfl
      · apply same_exact_event445
        · exact frames
        · have native : HEq
              (r.exactDecl.symm ▸ restoreOriginalHead r.original) (restoreOriginalHead r.original) :=
            dependent_transport_keeps_data445
              (P := fun d => SourceHead p.state.core p.root d) r.exactDecl.symm _
          exact native.symm.trans (heq_of_eq source.head.symm)
        · intro i
          have same : i = r.i0 := Fin.ext (by
            have lt := Nat.lt_of_lt_of_eq i.isLt r.onlyOutput
            change i.val = 0
            omega)
          subst i
          change HEq out (r.event.outputs r.i0)
          exact dependent_transport_keeps_data445
            (P := fun f => NamedMixedOutput401 p.state.b6 f r.i0) frames.symm _
  · rename_i notOne
    exact (notOne _ only).elim


theorem own_original_ref_reconstructs_checked_output445
    {s : I72.State} {q : I72.Request} {f : AuthoredBodyFrame393 s.core q}
    {i : Fin q.demand.outputs.length} (a : OriginalOutput (s := s) f i) :
    replayedOriginalRef442 a.key a.rowBinder a.valueBinder a.bodyId a.independent a.named =
      some ⟨a,rfl,rfl,rfl,rfl⟩ := by

  rcases a with ⟨key,rowBinder,valueBinder,different,use,mode,table,bodyId,supplied,annot,rowCap,
    valueCap,row,value⟩
  have ready : readRefPlan442 (refPlan key rowBinder valueBinder use mode table) =
      some ⟨use,mode,table,rfl⟩ := rfl
  unfold replayedOriginalRef442
  simp only [OriginalOutput.named]
  split
  · rw [ready]
    simp only [bind,Option.bind]
    split
    · rename_i r v atRow atValue
      have rEq := Option.some.inj (atRow.symm.trans row)
      have vEq := Option.some.inj (atValue.symm.trans value)
      subst r
      subst v
      rfl
    · rename_i wrong
      exact (wrong _ _ row value).elim
  · rename_i no
    exact (no rfl).elim


theorem readOwn_reconstructs_actual_source_output445 {p : Problem} (r : Replay p)
    (chosen : ReplayReadOwnOutput r) : r.readOwnRefOutput = some chosen := by
  rcases chosen with ⟨bodyId,cert⟩
  have exactOut := original_replayed_ref_equates_same_event_output442 r cert.out
  unfold Replay.readOwnRefOutput
  rw [← exactOut]
  rcases cert with ⟨a,hkey,hrow,hvalue,hbody⟩
  rcases a with ⟨key,rowB,valB,sep,use,mode,table,id,supplied,typed,rowCap,valCap,row,val⟩
  dsimp at hkey hrow hvalue hbody
  subst key rowB valB bodyId
  let own : OriginalOutput (s := p.state) r.event.frame r.i0 :=
    ⟨r.original.key,r.original.rowBinder,r.original.valueBinder,sep,use,mode,table,id,
      supplied,typed,rowCap,valCap,row,val⟩
  change (replayedOriginalRef442 own.key own.rowBinder own.valueBinder own.bodyId own.independent
    own.named).map (fun out => (⟨own.bodyId,out⟩ : ReplayReadOwnOutput r)) = some ⟨own.bodyId,⟨own,rfl,rfl,rfl,rfl⟩⟩
  rw [own_original_ref_reconstructs_checked_output445]
  rfl

theorem ready_source_exact_readSource445 {p : Problem}
    (source : SourceSelection p) (w : RefPositions441.Wire)
    (header : MergedOutput439.checkHeader439 p.state.core.current.environment = true)
    (loc : p.state.core.origins[w.original]? = some source.origin.original.original)
    (escape : List410.checkExactEscape p.state.core.current.ordinary
      source.origin.original.arg.lower w.escape = true)
    (canonicalPlacement : source.origin.event.frame.placement = unusedPlacement403) :
    readSource p w = some source := by
  have got := replay_selected_frame_from_finite_facts445 source w header loc escape canonicalPlacement
  unfold readSource
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


/-- Source-ready global declarations, separately from the selected
body. The last premise records the existing conservative syntax
check for each real declaration (it is not a successful replay). -/
structure HeaderReady445 (env : Environment) : Prop where
  roles : GeneralSourceMetadataRoles291.Valid env.source.roles
  coverage : GeneralDeclarativeWitnessModeCoverage357.Coverage env
  declarationIds : (env.source.declarations.map GeneralDeclarations.Declaration.id).Nodup
  declarationSyntax : ∀ d ∈ env.source.declarations, MergedOutput439.checksDeclaration439 env d = true

theorem ready_header_check445 {env : Environment} (h : HeaderReady445 env) :
    MergedOutput439.checkHeader439 env = true := by
  unfold MergedOutput439.checkHeader439
  exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr
    ⟨(GeneralSourceMetadataRoles291.check_exact _).mpr h.roles,
      (GeneralDeclarativeWitnessModeCoverage357.check_exact h.roles).mpr h.coverage⟩,
    Bool.and_eq_true_iff.mpr ⟨decide_eq_true h.declarationIds,List.all_eq_true.mpr h.declarationSyntax⟩⟩

open GeneralDeclarativeBounds319 (Bound)
open GeneralDeclarativeK2Graph321 (Shape)
open GeneralDeclarativeGraphRows321 (shapeOf)
open GeneralDeclarativeWitnessRank350 (rank atom)

/-- A raw finite escape table needs independent correctness against
the actual ordinary and structural rows. Merely having no K2 cycle
need not imply existence of such a table. -/
structure EscapeReady445 (s : GeneralDeclarativeHead320.State) (site : Nat)
    (w : List410.ExactEscapeWire) : Prop where
  monotone : ∀ a b, Bound s.normal a b → rank w.ranks a ≤ rank w.ranks b
  flat : ∀ e ∈ s.equations, ∀ n, e.right = .variable n → rank w.ranks e.left = rank w.ranks n
  rootSide : w.side site = 0
  reaches : ∀ e ∈ s.equations, ∀ h : Shape, shapeOf e.right = some h →
    w.side e.left ≤ 1 → ∀ n ∈ h.children, w.side n = 1

theorem ready_escape_check445 {s site w} (h : EscapeReady445 s site w) :
    List410.checkExactEscape s site w = true := by
  unfold List410.checkExactEscape List410.aliasRanks
  refine Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr
    ⟨Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨?_,?_⟩,?_⟩,
      decide_eq_true h.rootSide⟩,?_⟩
  · apply List.all_eq_true.mpr
    intro a present
    cases a with
    | rowLe => rfl
    | tyLe lo hi =>
      cases lo <;> cases hi <;>
        first | rfl | exact decide_eq_true (h.monotone _ _ (.constraint present))
  · apply List.all_eq_true.mpr
    rintro ⟨a,b⟩ present
    exact decide_eq_true (h.monotone _ _ (.interval present))
  · apply List.all_eq_true.mpr
    intro e present
    unfold List410.aliasRow
    split
    · rename_i n seen
      exact decide_eq_true (h.flat e present n seen)
    · rfl
  · apply List.all_eq_true.mpr
    intro e present
    unfold List410.exactShapeEscape
    split
    · rfl
    · rename_i head decoded
      split
      · rename_i reached
        apply List.all_eq_true.mpr
        intro n used
        exact decide_eq_true (h.reaches e present head decoded reached n used)
      · rfl

/-- This is genuine conditional concretization from source-stage facts,
not a premise that the selected-output reader succeeds. A proof that
every independent LocalSelection has these facts remains separate. -/
theorem canonical_ready_supplies_witness445 (p : FullProblem)
    (a : LocalSelection p.state p.root)
    (header : HeaderReady445 p.state.base.core.current.environment)
    (place : a.source.origin.event.frame.placement = unusedPlacement403)
    (escape : ∃ table, EscapeReady445 p.state.base.core.current.ordinary
      a.source.origin.original.arg.lower table) :
    ∃ w : Witness, check_full p a.report w = true := by
  obtain ⟨table,safe⟩ := escape
  obtain ⟨position,found⟩ := List.mem_iff_getElem?.mp a.source.origin.original.authored
  let w : RefPositions441.Wire := ⟨position,table⟩
  exact ⟨.mixedOutput w,actual_replay_reifies_local_witness445 p a w
    (ready_source_exact_readSource445 a.source w (ready_header_check445 header)
      found (ready_escape_check445 safe) place)⟩


end Yulang.GeneralDeclarativeI65.I72.RetainedFull445
