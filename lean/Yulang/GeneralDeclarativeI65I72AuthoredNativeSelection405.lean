import Yulang.GeneralDeclarativeI65I72GroundedExactTrace405

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72
open GeneralDeclarativeI65
open CommonRoleOutermostResolver (All₂ Dictionary Result Summarizes Tree)
open CommonRecursiveNominalIntervals (Endpoint)
open CommonDeclaredNominalInspection (Parameter)
open Core.PresenceGeneration (TyTerm)
open GeneralDeclarations (Declaration Checked)
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarativeWitnessModeCoverage357 (DeclarationCovered)
open GeneralDeclarativeWitnessConstructorModes357 (Use)
open GeneralDeclarativeDemand320 (Bounds)

def authoredUnaryPattern405 (key binder : Nat) : Pattern := .app key [.var binder]

/-- Independently authored source operands for one literal, declared
covariant unary candidate. No center is consulted to assess its
head; it is read separately when emitting that chosen lexical frame. -/
structure AuthoredUnaryChoice405 (s : State) (q : Request) (row : Declaration) where
  key : Nat
  binder : Nat
  interval : Capture
  writtenArgs : q.demand.arguments = [interval]
  writtenHead : row.head = [authoredUnaryPattern405 key binder]
  visibleOnly : visible s.core q = [row]
  checked : Checked (authoredRegistry s.core.current)
  covered : DeclarationCovered s.core.current.environment row
  use : Use s.core.current.environment key 1
  mode : use.mode = .declared [coValue404]
  table : s.core.modes[key]? = some [coValue404]
  win : ModeWindow s.core interval (authoredUnaryPattern405 key binder)
  left : Nat
  right : Nat
  literalLower : win.lower.endpoint = unaryNominalPoint404 key left
  literalUpper : win.upper.endpoint = unaryNominalPoint404 key right

/-- This is post-choice syntax, not a test for whether to select.
The already authored actual center is sufficient for this result;
an absent authored center here is *not* a language refusal. -/
structure UnaryActualPayload405 {s q row} (test : AuthoredUnaryChoice405 s q row) where
  payload : Capture
  projected : ValueBind s.core payload (.var test.left) (.var test.right)
  inInterval : Bounds s.core.current.ordinary payload
  actual : Origin
  authored : actual ∈ s.core.origins
  route : OriginRoute s.core actual test.interval.center
  literalCenter : actual.endpoint = unaryNominalPoint404 test.key payload.center

def UnaryActualPayload405.names {s q row} {test : AuthoredUnaryChoice405 s q row}
    (a : UnaryActualPayload405 test) : Nat → Capture :=
  fun n => if n = test.binder then a.payload else emptyCapture403

def native_unary_source_head405 {s q row} (test : AuthoredUnaryChoice405 s q row)
    (payload : UnaryActualPayload405 test) : SourceHead s.core q row := by
  refine .ordered payload.names ?_
  rw [test.writtenArgs,test.writtenHead]
  apply All₂.cons _ .nil
  apply DeepHead.declared test.win
  rw [test.literalLower,test.literalUpper]
  change DeepRead s.core payload.names false (.app test.key [.var test.binder])
    (.nominal test.key [.inl (.point (.ordinary (.var test.left)))])
    (.nominal test.key [.inl (.point (.ordinary (.var test.right)))])
    [.value test.binder (.var test.left) (.var test.right)]
  refine .nominal test.use ?_ test.table ?_
  · rw [test.mode]; rfl
  · have cap : ValueBind s.core (payload.names test.binder) (.var test.left) (.var test.right) := by
      simpa [UnaryActualPayload405.names] using payload.projected
    have parts : DeepArguments s.core payload.names false [coValue404] [.var test.binder]
        [.inl (.point (.ordinary (.var test.left)))] [.inl (.point (.ordinary (.var test.right)))]
        ([.value test.binder (.var test.left) (.var test.right)] ++ []) :=
      .cons (.covariantValue (.bind cap)) .nil
    simpa only [List.append_nil] using parts

def authoredNativeCandidate405 {s q row} (test : AuthoredUnaryChoice405 s q row)
    (payload : UnaryActualPayload405 test) : AuthoredCandidate s.core q row :=
  let inScope : row ∈ visible s.core q := by simp [test.visibleOnly]
  ⟨inScope,test.covered,(test.checked.2 row ((visible_exact s.core q row).mp inScope).1).signature,
    native_unary_source_head405 test payload⟩

def authoredNativeTape405 {s q row} (test : AuthoredUnaryChoice405 s q row)
    (payload : UnaryActualPayload405 test) : CandidateTape s.core q (visible s.core q) :=
  test.visibleOnly.symm ▸ .next (.matched (authoredNativeCandidate405 test payload)) .nil

theorem authoredNativeTape_exact405 {s q row} (test : AuthoredUnaryChoice405 s q row)
    (payload : UnaryActualPayload405 test) (safe : ¬RootCycle s q) :
    TapedMatch s.core q (authoredNativeTape405 test payload) row := by
  have eq : ∀ xs (h : xs = [row]),
      let tape : CandidateTape s.core q xs := h.symm ▸
        .next (.matched (authoredNativeCandidate405 test payload)) .nil
      tape.waits = false ∧ tape.live = [row] := by
    intro xs h
    subst xs
    exact ⟨rfl,rfl⟩
  exact ⟨safe,(eq _ test.visibleOnly).1,(eq _ test.visibleOnly).2⟩

/-- Native branch evidence indexed by the exact event and source tape.
Its entered position is computed from the real declaration coordinate
and original lower input; it does not carry an arbitrary visits list. -/
structure AuthoredNativeSelected405 {s q} (e : Event s q) where
  test : AuthoredUnaryChoice405 s q e.frame.decl
  payload : UnaryActualPayload405 test
  origin : SelectedHeadOrigin395 (row := e.frame.decl) (authoredNativeTape405 test payload)
  frame : e.frame = preoutputFrameOfOrigin399 origin unusedPlacement403 (fun _ => emptyCapture403)
  head : e.head = origin.pick.head

def AuthoredNativeSelected405.visits {s q e} (read : AuthoredNativeSelected405 (s := s) (q := q) e) :
    List CandidateVisit :=
  [⟨read.origin.rawOrdinal,0,[],.value,false,read.test.interval.lower⟩]

theorem actual_authored_native_priority_405 {s q e}
    (read : AuthoredNativeSelected405 (s := s) (q := q) e) (safe : ¬RootCycle s q) :
    ∃ site, read.visits = [site] ∧ ¬CurrentCycleAt s site.site ∧
      site.declarationOrdinal = e.frame.ordinal ∧ site.path = [] ∧
      e.frame.decl.head[site.argumentOrdinal]? = some (authoredUnaryPattern405 read.test.key read.test.binder) ∧
      ∀ view root below, ¬GeneralDeclarativeInspect321.Visit view root (.variable read.test.binder) below := by
  let visit : CandidateVisit := ⟨read.origin.rawOrdinal,0,[],.value,false,read.test.interval.lower⟩
  have original : read.origin.rawOrdinal = e.frame.ordinal :=
    (congrArg AuthoredBodyFrame393.ordinal read.frame).symm
  exact ⟨visit,rfl,fun cycle => safe ⟨read.test.interval,by simp [read.test.writtenArgs],cycle⟩,
    original,rfl,by simp [visit,read.test.writtenHead],
    fun _ _ _ => GeneralDeclarativeInspect321.variable_has_no_visit⟩

def authoredNativeSelectedSource405 : SourcePrimitives where
  elected := fun s q e needs => completedChoiceSource404.elected s q e needs ∨
    needs = [] ∧ Nonempty (AuthoredNativeSelected405 e) ∧
      (RetainedVariableOutputs403 e ∨ RetainedTypedValueRows403 e)
  other := completedChoiceSource404.other

theorem authored_native_source_provides_nodes405 : S10 authoredNativeSelectedSource405 := by
  intro s q e needs raw rule support
  rcases rule with ordinary|native
  · have supplied : completedChoiceSource404.elected s q e needs := ordinary
    -- The node readback uses the elected source evidence, not a model.
    rcases supplied with old|new
    · obtain ⟨read⟩ := old.2.1
      have checked := read.elected.scope.checked.2 e.frame.decl (List.mem_of_getElem? e.frame.authored)
      refine node_from_exact_preoutput_head405 e checked (fun _ => emptyCapture403) ?_
      rw [read.sameHead]
      exact congrArg AuthoredBodyFrame393.input read.sameFrame
    · obtain ⟨read⟩ := new.1
      exact supporting_readback_makes_actual_node404 read
  · obtain ⟨read⟩ := native.2.1
    have checked := read.test.checked.2 e.frame.decl (List.mem_of_getElem? e.frame.authored)
    refine node_from_exact_preoutput_head405 e checked (fun _ => emptyCapture403) ?_
    rw [read.head]
    exact congrArg AuthoredBodyFrame393.input read.frame

theorem authored_native_source_keeps_own_fixed_rows405 : KeepsFixedOutputs404 authoredNativeSelectedSource405 :=
  fun s q e needs elected => elected.elim (completed_choice_keeps_fixed_rows404 s q e needs) (fun native => native.2.2)

theorem authored_native_dictionary_reuses_given_trace405 {s q t e d}
    (trace : SourceTrace authoredNativeSelectedSource405 s q t e)
    (summary : Summarizes t (.selected d)) :
    ∃ tree : I72.GeneralTree trace d,
      CanonicalReplay tree tree.ledger ∧ ∀ m, Fits s m → DictionaryEvidence s m q d := by
  obtain ⟨⟨tree⟩,shown⟩ := (lower_selected_at_exact_trace _ s
    (authored_native_source_provides_nodes405 s)).tree trace summary
  have same : CanonicalReplay tree tree.ledger := ⟨rfl,shown,rfl⟩
  refine ⟨tree,same,?_⟩
  intro m fit
  have meaning := typed_replay_keeps_same_event_meaning _ s q t e d trace tree tree.ledger m same
    (general_tree_meaning_from_local _ semantic_node_in_signature s q t e d trace tree m fit)
  exact exact_ledger_evidence405 tree.ledger m meaning
    (fixed_targets_from_own_elected_events405 authored_native_source_keeps_own_fixed_rows405 tree m fit)

theorem dictionary_sound_for_authored_native_unary405 : DictionarySound authoredNativeSelectedSource405 := by
  intro s q d chosen m fit
  obtain ⟨t,_,source,summary⟩ := classifies_unpacks_source_in_signature _ s q d chosen
  obtain ⟨_,_,exact⟩ := authored_native_dictionary_reuses_given_trace405 source.source summary
  exact exact m fit

/-- A direct source constructor with genuinely nonempty candidate
visits, unlike the just-variable projection. It is not the native
completed-lower case, arbitrary rows, or an implementation fixture.
Raw K2 is checked independently; the authored center is read only
to form the exact payload and chosen preoutput body. -/
theorem chosen_authored_native_unary_has_nonempty_actual_visits405 {s q row}
    (test : AuthoredUnaryChoice405 s q row) (payload : UnaryActualPayload405 test)
    (safe : ¬RootCycle s q) (noWhere : row.requirements = []) (noOutputs : q.demand.outputs = []) :
    ∃ (e : Event s q) (native : AuthoredNativeSelected405 e) (kidTrees : List Tree)
        (trace : SourceTrace authoredNativeSelectedSource405 s q (.selected e.frame.decl.id kidTrees) (some e)),
      e.frame.decl = row ∧
      Summarizes (.selected e.frame.decl.id kidTrees) (.selected (.node row.id [])) ∧
      (∃ site, native.visits = [site] ∧ ¬CurrentCycleAt s site.site ∧ site.declarationOrdinal = e.frame.ordinal) ∧
      ∃ tree : I72.GeneralTree trace (.node row.id []),
        CanonicalReplay tree tree.ledger ∧ ∀ m, Fits s m → DictionaryEvidence s m q (.node row.id []) := by
  have absent : ∀ i : Fin q.demand.outputs.length, False := by
    intro i
    obtain ⟨n,absurd⟩ := i
    simp [noOutputs] at absurd
  obtain ⟨origin⟩ := selected_head_original_origin395 (authoredNativeTape_exact405 test payload safe)
  let event : Event s q :=
    ⟨preoutputFrameOfOrigin399 origin unusedPlacement403 (fun _ => emptyCapture403),
      origin.pick.head,fun i => (absent i).elim⟩
  let native : AuthoredNativeSelected405 event := ⟨test,payload,origin,rfl,rfl⟩
  have chosen : authoredNativeSelectedSource405.elected s q event [] :=
    .inr ⟨rfl,⟨native⟩,.inl (fun i => (absent i).elim)⟩
  have kids : event.kids = [] := by
    simp [Event.kids,event,frameWhereKids400,AuthoredBodyFrame393.clauses,
      preoutputFrameOfOrigin399,frameAtSource395,noWhere,children]
  let trace : SourceTrace authoredNativeSelectedSource405 s q (.selected event.frame.decl.id []) (some event) :=
    .selected event safe chosen .nil (kids.symm ▸ .nil)
  have done : Summarizes (.selected event.frame.decl.id []) (.selected (.node row.id [])) :=
    .selected .nil (.selected rfl)
  obtain ⟨site,visits,uncyclic,ordinal,_,_,_⟩ := actual_authored_native_priority_405 native safe
  exact ⟨event,native,[],trace,rfl,done,⟨site,visits,uncyclic,ordinal⟩,
    authored_native_dictionary_reuses_given_trace405 trace done⟩

private theorem authored_unary_child_is_literal_var405 {s q row}
    (known : AuthoredUnaryChoice405 s q row) {d key child}
    (visibleRow : d ∈ visible s.core q) {written : Pattern}
    (head : d.head = [written]) (dispatch : normalize written = .app key [child]) :
    child = .var known.binder := by
  rw [known.visibleOnly] at visibleRow
  cases List.mem_singleton.mp visibleRow
  have shape : written = authoredUnaryPattern405 known.key known.binder :=
    (List.cons.inj (head.symm.trans known.writtenHead)).1
  rw [shape] at dispatch
  change Pattern.app known.key [.var known.binder] = Pattern.app key [child] at dispatch
  exact (List.cons.inj (Pattern.app.inj dispatch).2).1.symm

/-- In this one-row native fragment the previously represented K2
branches cannot have entered a structural child: the only written
child is literally a variable. The inherited ambiguity branch has
no second visible declaration. This does not test a center or rule
out an unrepresented general native search. -/
theorem authored_unary_inherits_no_competing_local_diagnostic405 {s q row verdict needs}
    (test : AuthoredUnaryChoice405 s q row) :
    ¬ completedChoiceSource404.other s q verdict needs := by
  rintro (prior | ambiguous)
  · rcases prior with plain|completed
    · rcases plain.2 with repeats|authored
      · cases repeats with
        | ambiguous _ atLeast => simp [test.visibleOnly] at atLeast
      · obtain ⟨_,_,site,_⟩ := authored
        have inner := authored_unary_child_is_literal_var405 test site.visibleRow site.exactHead site.dispatch
        have translated := site.literalQuery
        rw [inner] at translated
        change some (GeneralNominalCenteredHeadMatExpressions.Expr.variable test.binder) = some site.query at translated
        have inspects := site.enters
        rw [← Option.some.inj translated] at inspects
        cases inspects
    · obtain ⟨_,⟨site⟩⟩ := completed
      have inner := authored_unary_child_is_literal_var405 test site.entry.visibleRow
        site.entry.exactHead site.entry.dispatch
      have translated := site.entry.exactChild
      rw [inner] at translated
      change some (GeneralNominalCenteredHeadMatExpressions.Expr.variable test.binder) = some site.entry.query at translated
      have inspects := site.entry.inspecting
      rw [← Option.some.inj translated] at inspects
      cases inspects
  · obtain ⟨_,⟨rivals⟩⟩ := ambiguous
    have count := rivals.two
    simp [test.visibleOnly] at count

theorem actual_authored_native_tape_keeps_exact_source_pick405 {s q row}
    {test : AuthoredUnaryChoice405 s q row} {payload : UnaryActualPayload405 test}
    (origin : SelectedHeadOrigin395 (row := row) (authoredNativeTape405 test payload)) :
    origin.pick = authoredNativeCandidate405 test payload ∧ origin.visibleOrdinal = 0 := by
  have one : ∀ rows (eq : rows = [row]),
      let t : CandidateTape s.core q rows := eq.symm ▸ .next
        (.matched (authoredNativeCandidate405 test payload)) .nil
      storedCandidateEntries401 t = [(0,⟨row,authoredNativeCandidate405 test payload⟩)] := by
    intro rows eq
    subst rows
    rfl
  have h := original_stored_entry_is_listed401 origin.stored
  change (origin.visibleOrdinal,⟨row,origin.pick⟩) ∈
    storedCandidateEntries401 (authoredNativeTape405 test payload) at h
  unfold authoredNativeTape405 at h
  rw [one _ test.visibleOnly] at h
  have equal := List.mem_singleton.mp h
  exact ⟨eq_of_heq (Sigma.mk.inj (congrArg Prod.snd equal)).2,congrArg Prod.fst equal⟩

/-- Given an independently authored actual payload indication, it is
that very logical center and original term which the same selected
node retains. The guard-only relation cannot supply this fact. -/
theorem actual_authored_native_uses_original_payload_center405 {s q e}
    (read : AuthoredNativeSelected405 (s := s) (q := q) e) :
    e.frame.input read.test.binder = read.payload.payload ∧
    ∀ m, Fits s m →
      m.nativeSyntax read.payload.actual.slot = some (unaryNominalPoint404 read.test.key
        (e.frame.input read.test.binder).center) := by
  have same := (actual_authored_native_tape_keeps_exact_source_pick405 read.origin).1
  have cap : e.frame.input read.test.binder = read.payload.payload := by
    rw [congrArg AuthoredBodyFrame393.input read.frame]
    change preoutputInputOfHead399 read.origin.pick.head (fun _ => emptyCapture403) _ = _
    rw [same]
    change read.payload.names read.test.binder = read.payload.payload
    simp [UnaryActualPayload405.names]
  refine ⟨cap,fun m fit => ?_⟩
  rw [cap,← read.payload.literalCenter]
  exact fit.2 _ read.payload.authored

/-- The nonempty, actual one-row native route can also retain the
literal B6 body and ordered recursive where children. A well-formed
input alone neither derives the B6 occurrence input from scratch
nor makes its fixed output true in the current State. -/
theorem authored_native_selects_with_original_B6_and_where405 {s q row ds}
    (test : AuthoredUnaryChoice405 s q row) (payload : UnaryActualPayload405 test) (safe : ¬RootCycle s q)
    (declared : DeclaredOriginalOutputs400 s.core q)
    (typed : ∀ origin : SelectedHeadOrigin395 (row := row) (authoredNativeTape405 test payload),
      NamedInputAtStoredHead401 s.b6 (preoutputFrameOfOrigin399 origin unusedPlacement403 (fun _ => emptyCapture403)))
    (fixed : ∀ origin : SelectedHeadOrigin395 (row := row) (authoredNativeTape405 test payload),
      let f := preoutputFrameOfOrigin399 origin unusedPlacement403 (fun _ => emptyCapture403)
      RetainedOutputSources403 (s := s) f ∨ TypedRowsAtOriginalInput403 (s := s) f)
    (whereDerives : ∀ origin : SelectedHeadOrigin395 (row := row) (authoredNativeTape405 test payload),
      let f := preoutputFrameOfOrigin399 origin unusedPlacement403 (fun _ => emptyCapture403)
      ∃ trees : List Tree, Nonempty (WhereForest authoredNativeSelectedSource405 s (frameWhereKids400 f) trees) ∧
        All₂ Summarizes trees (ds.map Result.selected)) :
    ∃ (e : Event s q) (read : AuthoredNativeSelected405 e) (trees : List Tree)
        (trace : SourceTrace authoredNativeSelectedSource405 s q (.selected e.frame.decl.id trees) (some e))
        (tree : I72.GeneralTree trace (.node row.id ds)),
      Summarizes (.selected e.frame.decl.id trees) (.selected (.node row.id ds)) ∧
      LedgerMeaning ExactSourceRhs tree.ledger ∧
      (∃ site, read.visits = [site] ∧ ¬CurrentCycleAt s site.site) ∧
      CanonicalReplay tree tree.ledger ∧ ∀ m, Fits s m → DictionaryEvidence s m q (.node row.id ds) := by
  obtain ⟨origin⟩ := selected_head_original_origin395 (authoredNativeTape_exact405 test payload safe)
  obtain ⟨out,_,_,_⟩ := stored_head_emits_exact_ordered_mixed_values401
    origin unusedPlacement403 (fun _ => emptyCapture403) test.checked declared s.b6 (typed origin)
  let e : Event s q := ⟨preoutputFrameOfOrigin399 origin unusedPlacement403 (fun _ => emptyCapture403),
    origin.pick.head,out⟩
  let read : AuthoredNativeSelected405 e := ⟨test,payload,origin,rfl,rfl⟩
  have rows : RetainedVariableOutputs403 e ∨ RetainedTypedValueRows403 e :=
    (fixed origin).elim (fun alias => .inl (addressed_sources_give_real_output_rows403 e alias))
      (fun kinded => .inr (fun i => kinded i (out i)))
  have rule : authoredNativeSelectedSource405.elected s q e [] := .inr ⟨rfl,⟨read⟩,rows⟩
  obtain ⟨trees,⟨kids⟩,summ⟩ := whereDerives origin
  let trace : SourceTrace authoredNativeSelectedSource405 s q (.selected e.frame.decl.id trees) (some e) :=
    .selected e safe rule .nil kids
  have done : Summarizes (.selected e.frame.decl.id trees) (.selected (.node row.id ds)) :=
    .selected summ (.selected rfl)
  obtain ⟨tree,exact,meaning⟩ := authored_native_dictionary_reuses_given_trace405 trace done
  obtain ⟨site,visits,safeSite,_,_,_,_⟩ := actual_authored_native_priority_405 read safe
  exact ⟨e,read,trees,trace,tree,done,draft_ledger_already_has_the_original_B6_RHS405 _,
    ⟨site,visits,safeSite⟩,exact,meaning⟩

end Yulang.GeneralDeclarativeI65.I72
