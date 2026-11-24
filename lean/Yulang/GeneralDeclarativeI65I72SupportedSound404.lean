import Yulang.GeneralDeclarativeI65I72ProducerConsumer404

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72
open GeneralDeclarativeI65
open CommonRoleOutermostResolver (All₂ Dictionary Result Summarizes Tree)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarations (DeclarationChecked)

theorem supported_origin_is_actual404 {s q d needs}
    (choice : SupportedChoice404 s q d needs) (retained : SupportedCenters404 choice)
    (origin : SelectedHeadOrigin395 (row := d) (supportedTape404 choice retained)) :
    origin.pick = supportedCandidate404 choice retained ∧ origin.visibleOrdinal = 0 := by
  have one : ∀ rows (eq : rows = [d]),
      let t : CandidateTape s.core q rows := eq.symm ▸ .next
        (.matched (supportedCandidate404 choice retained)) .nil
      storedCandidateEntries401 t = [(0,⟨d,supportedCandidate404 choice retained⟩)] := by
    intro rows eq
    subst rows
    rfl
  have h := original_stored_entry_is_listed401 origin.stored
  change (origin.visibleOrdinal,⟨d,origin.pick⟩) ∈
    storedCandidateEntries401 (supportedTape404 choice retained) at h
  unfold supportedTape404 at h
  rw [one _ choice.sole] at h
  have equal := List.mem_singleton.mp h
  exact ⟨eq_of_heq (Sigma.mk.inj (congrArg Prod.snd equal)).2,congrArg Prod.fst equal⟩

private theorem exact_variable_node404 {s q} (e : Event s q)
    (check : DeclarationChecked (authoredRegistry s.core.current).constructors
      (authoredRegistry s.core.current).roles e.frame.decl)
    (captures : Nat → Capture)
    (sameInput : e.frame.input = captures)
    {readArgs : All₂ (DeepHead s.core captures) q.demand.arguments e.frame.decl.head}
    (looks : e.head = .ordered captures readArgs) : GeneralNode e := by
  refine ⟨check,?_⟩
  unfold CapturesActualHead
  rw [looks]
  intro n named
  change (e.frame.names.input n).center = (captures n).center
  have exact : e.frame.names.input n = e.frame.input n :=
    GeneralDeclarativeProducedNames325.exact_input check named
  rw [exact,sameInput]

private theorem authored_readback_node404 {s q e}
    (read : VariableWhereReadback403 (s := s) (q := q) e) : GeneralNode e := by
  have check := read.elected.scope.checked.2 e.frame.decl (List.mem_of_getElem? e.frame.authored)
  have stored := (repeated_origin_keeps_exact_candidate403 read.elected read.retained read.origin).1
  have actualHead := read.sameHead.trans (congrArg AuthoredCandidate.head stored)
  have actualFrame : e.frame.input = selectedInput403 q read.elected.row := by
    refine (congrArg AuthoredBodyFrame393.input read.sameFrame).trans ?_
    change preoutputInputOfHead399 read.origin.pick.head (fun _ => emptyCapture403) = _
    rw [stored]
    rfl
  exact exact_variable_node404 e check _ actualFrame actualHead

theorem supporting_readback_makes_actual_node404 {s q e needs}
    (read : SupportedEvent404 (s := s) (q := q) needs e) : GeneralNode e := by
  have check := read.choice.checked.2 e.frame.decl (List.mem_of_getElem? e.frame.authored)
  have stored := (supported_origin_is_actual404 read.choice read.retained read.origin).1
  have actualHead := read.head.trans (congrArg AuthoredCandidate.head stored)
  have actualFrame : e.frame.input = selectedInput403 q read.choice.row := by
    refine (congrArg AuthoredBodyFrame393.input read.frame).trans ?_
    change preoutputInputOfHead399 read.origin.pick.head (fun _ => emptyCapture403) = _
    rw [stored]
    rfl
  exact exact_variable_node404 e check _ actualFrame actualHead

theorem supported_source_provides_C402_nodes404 : S10 supportedVariableSource404 := by
  intro s q e needs safe rule forest
  rcases rule with old|new
  · obtain ⟨read⟩ := old.2.1
    exact authored_readback_node404 read
  · obtain ⟨read⟩ := new.1
    exact supporting_readback_makes_actual_node404 read

theorem supported_aligned_ledger_keeps_fixed_targets404 {s q t event d}
    {trace : SourceTrace supportedVariableSource404 s q t event}
    (lowered : I72.GeneralTree trace d) (m : Model) (fit : Fits s m) :
    LedgerMeaning (FixedTargets m) lowered.ledger := by
  exact I72.GeneralTree.rec (R := supportedVariableSource404) (s := s)
    (motive_1 := fun {q t e} trace d tr => LedgerMeaning (FixedTargets m) tr.ledger)
    (motive_2 := fun {qs ts} trace ds tr => LedgerForestMeaning (FixedTargets m) tr.ledger)
    (fun {q} {needs} {ts} {ds} {event} {rawSafe} {source} {support} {kids} witness forest below => by
      change FixedTargets m event ∧ _
      have just := supported_rules_keep_exact_rows404 s q event needs source
      exact ⟨just.elim (fun alias => retained_variable_targets_sound403 alias m fit)
        (fun typed => retained_typed_rows_satisfy_fixed_targets403 typed m fit),below⟩)
    True.intro
    (fun _ _ first later => ⟨first,later⟩)
    lowered

private theorem exact_supported_dictionary404 {s q d} (ledger : Ledger s q d) (m : Model) :
    LedgerMeaning (LocalMeaning m) ledger → LedgerMeaning (FixedTargets m) ledger →
      DictionaryEvidence s m q d := by
  exact Ledger.rec
    (motive_1 := fun q d t => LedgerMeaning (LocalMeaning m) t →
      LedgerMeaning (FixedTargets m) t → DictionaryEvidence s m q d)
    (motive_2 := fun qs ds fs => LedgerForestMeaning (LocalMeaning m) fs →
      LedgerForestMeaning (FixedTargets m) fs → DictionaryEvidenceForest s m qs ds)
    (fun e _ tail localProof fixed => .node e localProof.1 fixed.1 (tail localProof.2 fixed.2))
    (fun _ _ => .nil)
    (fun _ _ first later localProof fixed => .cons
      (first localProof.1 fixed.1) (later localProof.2 fixed.2))
    ledger

/-- The actual source derivation contains the smaller output producers;
the ledger keeps the ordered where children, not an accidental copy
of the separate support forest. The same ledger retains typed fixed
rows in every fitting model. No fit or checker is needed for election. -/
theorem supported_classifies_uses_one_C402_ledger404 {s q d}
    (chosen : Classifies supportedVariableSource404 s q (.selected d)) :
    ∃ (t : Tree) (event : Option (Event s q))
        (trace : SourceTrace supportedVariableSource404 s q t event)
        (lowered : I72.GeneralTree trace d) (ledger : Ledger s q d),
      Summarizes t (.selected d) ∧ CanonicalReplay lowered ledger ∧
      LedgerMeaning Addresses ledger ∧
      (∀ e (_first : event = some e) a, a ∈ q.demand.arguments →
        Nonempty (ReadyInput404 supportedVariableSource404 s a)) ∧
      ∀ m, Fits s m →
        LedgerMeaning (LocalMeaning m) ledger ∧ LedgerMeaning (FixedTargets m) ledger ∧
        DictionaryEvidence s m q d := by
  obtain ⟨t,_,source,summarizes⟩ := classifies_unpacks_source_in_signature
    supportedVariableSource404 s q d chosen
  obtain ⟨⟨lowered⟩,rendered⟩ := (lower_selected_at_exact_trace supportedVariableSource404 s
    (supported_source_provides_C402_nodes404 s)).tree source.source summarizes
  obtain ⟨ledger,same⟩ := typed_replay_alignment_in_signature supportedVariableSource404
    s q t source.event d source.source lowered rendered
  have addresses := typed_replay_keeps_original_addresses supportedVariableSource404
    s q t source.event d source.source lowered ledger same
  refine ⟨t,source.event,source.source,lowered,ledger,summarizes,same,addresses,?_,?_⟩
  · intro e eq a seen
    have actual : SourceTrace supportedVariableSource404 s q t (some e) := eq ▸ source.source
    exact actual_classifies_input404 actual a seen
  · intro m fit
    have exactMeaning := typed_replay_keeps_same_event_meaning supportedVariableSource404
      s q t source.event d source.source lowered ledger m same
      (general_tree_meaning_from_local supportedVariableSource404 semantic_node_in_signature
        s q t source.event d source.source lowered m fit)
    have exactFixed : LedgerMeaning (FixedTargets m) ledger := by
      rw [← same.1]
      exact supported_aligned_ledger_keeps_fixed_targets404 lowered m fit
    exact ⟨exactMeaning,exactFixed,exact_supported_dictionary404 ledger m exactMeaning exactFixed⟩

theorem completed_input_dictionary_sound404 : DictionarySound supportedVariableSource404 := by
  intro s q d selection m fit
  obtain ⟨_,_,_,_,_,_,_,_,_,final⟩ := supported_classifies_uses_one_C402_ledger404 selection
  exact (final m fit).2.2

end Yulang.GeneralDeclarativeI65.I72
