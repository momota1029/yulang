import Yulang.GeneralDeclarativeI65I72VariableWhere403

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72
open GeneralDeclarativeI65
open CommonRoleOutermostResolver (Dictionary Result Summarizes Tree)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)

/-- Instantiate the existing C402 lowering node with the very same
selected original source. The reported event cannot choose a new
capture independently of the derived input and actual tie rows. -/
theorem variable_where_provides_C402_nodes403 : S10 variableWhereSource403 := by
  intro s q e needs rawSafe source support
  obtain ⟨_,⟨read⟩,frames⟩ := source
  have checked := read.elected.scope.checked.2 e.frame.decl
    (List.mem_of_getElem? e.frame.authored)
  refine ⟨checked,?_⟩
  have stored := (repeated_origin_keeps_exact_candidate403 read.elected read.retained read.origin).1
  have actualHead := read.sameHead.trans (congrArg AuthoredCandidate.head stored)
  unfold CapturesActualHead
  rw [actualHead]
  change ∀ n ∈ e.frame.decl.inputNames,
    (e.frame.names.input n).center = (selectedInput403 q read.elected.row n).center
  intro n named
  have sameInput : e.frame.input = selectedInput403 q read.elected.row := by
    refine (congrArg AuthoredBodyFrame393.input read.sameFrame).trans ?_
    change preoutputInputOfHead399 read.origin.pick.head (fun _ => emptyCapture403) = _
    rw [stored]
    rfl
  have sameName : e.frame.names.input n = e.frame.input n :=
    GeneralDeclarativeProducedNames325.exact_input checked named
  rw [sameName,sameInput]

/-- The lowering stays indexed by the selected finite source trace;
read the fixed output fact from that trace, not an unrelated ledger
with the same dictionary keys or equal denoted values. -/
theorem variable_lowered_ledger_keeps_fixed_targets403 {s q t event d}
    {trace : SourceTrace variableWhereSource403 s q t event}
    (lowered : I72.GeneralTree trace d) (m : Model) (fit : Fits s m) :
    LedgerMeaning (FixedTargets m) lowered.ledger := by
  exact I72.GeneralTree.rec (R := variableWhereSource403) (s := s)
    (motive_1 := fun {q t e} trace d tr => LedgerMeaning (FixedTargets m) tr.ledger)
    (motive_2 := fun {qs ts} trace ds tr => LedgerForestMeaning (FixedTargets m) tr.ledger)
    (fun {q} {needs} {ts} {ds} {event} {rawSafe} {source} {support} {kids} witness forest below => by
      change FixedTargets m event ∧ _
      exact ⟨retained_variable_targets_sound403 source.2.2 m fit,below⟩)
    True.intro
    (fun _ _ first later => ⟨first,later⟩)
    lowered

private theorem exact_ledger_dictionary403 {s q d} (ledger : Ledger s q d) (m : Model) :
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

/-- Exact original C402 replay connected to the concrete source rule.
Choose the ordered ledger without reference to a model, then prove
the very same ledger's semantic/retained outputs in *each* fitted
model and construct the unchanged dictionary meaning. -/
theorem concrete_source_uses_C402_exact_replay403 {s q d}
    (chosen : Classifies variableWhereSource403 s q (.selected d)) :
    ∃ (t : Tree) (event : Option (Event s q))
        (trace : SourceTrace variableWhereSource403 s q t event)
        (lowered : I72.GeneralTree trace d) (ledger : Ledger s q d),
      Summarizes t (.selected d) ∧ CanonicalReplay lowered ledger ∧
      LedgerMeaning Addresses ledger ∧
      ∀ m, Fits s m →
        LedgerMeaning (LocalMeaning m) ledger ∧ LedgerMeaning (FixedTargets m) ledger ∧
        DictionaryEvidence s m q d := by
  obtain ⟨t,_,source,summarizes⟩ := classifies_unpacks_source_in_signature
    variableWhereSource403 s q d chosen
  obtain ⟨⟨lowered⟩,rendered⟩ := (lower_selected_at_exact_trace variableWhereSource403 s
    (variable_where_provides_C402_nodes403 s)).tree source.source summarizes
  obtain ⟨ledger,same⟩ := typed_replay_alignment_in_signature variableWhereSource403
    s q t source.event d source.source lowered rendered
  have addresses := typed_replay_keeps_original_addresses variableWhereSource403
    s q t source.event d source.source lowered ledger same
  refine ⟨t,source.event,source.source,lowered,ledger,summarizes,same,addresses,?_⟩
  intro m fit
  have exactMeaning := typed_replay_keeps_same_event_meaning variableWhereSource403
    s q t source.event d source.source lowered ledger m same
    (general_tree_meaning_from_local variableWhereSource403 semantic_node_in_signature
      s q t source.event d source.source lowered m fit)
  have exactFixed : LedgerMeaning (FixedTargets m) ledger := by
    rw [← same.1]
    exact variable_lowered_ledger_keeps_fixed_targets403 lowered m fit
  exact ⟨exactMeaning,exactFixed,exact_ledger_dictionary403 ledger m exactMeaning exactFixed⟩

end Yulang.GeneralDeclarativeI65.I72
