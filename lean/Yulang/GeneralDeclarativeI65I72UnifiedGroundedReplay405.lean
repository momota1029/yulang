import Yulang.GeneralDeclarativeI65I72AuthoredNativeSelection405

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72
open GeneralDeclarativeI65
open CommonRoleOutermostResolver (Dictionary Summarizes Tree)

/-- Both actual selected source rules have computed, not stored,
visits. The exact given support forest remains the derivation index.
A certificate for a different event or outcome is not a constructor. -/
inductive ChosenScan405 {s q} (e : Event s q) {needs}
    (support : SupportForest authoredNativeSelectedSource405 s needs) : Type
  | variableCase : GroundedSelection405 authoredNativeSelectedSource405 e needs support → ChosenScan405 e support
  | nominal : AuthoredNativeSelected405 e → ChosenScan405 e support

def ChosenScan405.visits {s q e needs support}
    (scan : ChosenScan405 (s := s) (q := q) e (needs := needs) support) : List CandidateVisit :=
  match scan with
  | .variableCase read => read.scan.visits
  | .nominal read => read.visits

structure ScopePriority405 {s q e needs} (support : SupportForest authoredNativeSelectedSource405 s needs) : Prop where
  raw : ¬RootCycle s q
  byActualRule : ∃ scan : ChosenScan405 (e : Event s q) support,
    ∀ inspected ∈ scan.visits, inspected.declarationOrdinal = e.frame.ordinal ∧ ¬ CurrentCycleAt s inspected.site

theorem exact_chosen_scan_has_raw_priority405 {s q e needs support}
    (scan : ChosenScan405 (s := s) (q := q) e (needs := needs) support) (safe : ¬RootCycle s q) :
    ScopePriority405 (e := e) support := by
  refine ⟨safe,scan,?_⟩
  intro site enter
  cases scan with
  | variableCase read =>
    have empty := variable_scan_visits_exact405 read.scan
    change site ∈ read.scan.visits at enter
    rw [empty] at enter
    cases enter
  | nominal read =>
    obtain ⟨actual,visited,uncyclic,atI,_,_,_⟩ := actual_authored_native_priority_405 read safe
    change site ∈ read.visits at enter
    rw [visited] at enter
    cases List.mem_singleton.mp enter
    exact ⟨atI,uncyclic⟩

/-- Assemble the precise priority at the same positive primitive
case under which the actual source trace stores its support forest.
A wrongly inferred visit set cannot be supplied as an argument. -/
theorem authored_and_variable_rules_ground_the_same_trace405 {s q e needs}
    (safe : ¬RootCycle s q) (primitive : authoredNativeSelectedSource405.elected s q e needs)
    (support : SupportForest authoredNativeSelectedSource405 s needs) :
    ScopePriority405 (e := e) support := by
  rcases primitive with plain|native
  · rcases plain with old|fresh
    · obtain ⟨source⟩ := old.2.1
      let witnessed : GroundedSelection405 authoredNativeSelectedSource405 e needs support :=
        ⟨selectedRepeatedTape403 source.elected source.retained,source.origin,
          (congrArg AuthoredBodyFrame393.ordinal source.sameFrame).symm,source.sameHead.symm,
          single_variable_scan405 _ source.elected.sole
            (selectedRepeatedCandidate403 source.elected source.retained) source.elected.row,
          source.elected.sole⟩
      exact exact_chosen_scan_has_raw_priority405 (.variableCase witnessed) safe
    · obtain ⟨source⟩ := fresh.1
      let witnessed : GroundedSelection405 authoredNativeSelectedSource405 e needs support :=
        ⟨supportedTape404 source.choice source.retained,source.origin,
          (congrArg AuthoredBodyFrame393.ordinal source.frame).symm,source.head.symm,
          single_variable_scan405 _ source.choice.sole
            (supportedCandidate404 source.choice source.retained) source.choice.row,
          source.choice.sole⟩
      exact exact_chosen_scan_has_raw_priority405 (.variableCase witnessed) safe
  · obtain ⟨read⟩ := native.2.1
    exact exact_chosen_scan_has_raw_priority405 (.nominal read) safe

mutual
def CompleteScopePriority405 {s q t e} (trace : SourceTrace authoredNativeSelectedSource405 s q t e) : Prop :=
  match trace with
  | .rootK2 _ => True
  | .other _ _ _ support => CompleteScopeProducer405 support
  | .selected e _ _ support kids =>
    ScopePriority405 (e := e) support ∧ CompleteScopeProducer405 support ∧ CompleteScopeWhere405 kids

def CompleteScopeWhere405 {s qs ts} (forest : WhereForest authoredNativeSelectedSource405 s qs ts) : Prop :=
  match forest with
  | .nil => True
  | .cons first later => CompleteScopePriority405 first ∧ CompleteScopeWhere405 later

def CompleteScopeProducer405 {s needs} (forest : SupportForest authoredNativeSelectedSource405 s needs) : Prop :=
  match forest with
  | .nil => True
  | .cons literal _ _ later => CompleteScopePriority405 literal ∧ CompleteScopeProducer405 later
end

theorem all_actual_selected_native_or_variable_nodes_have_priority405
    {s q t e} (trace : SourceTrace authoredNativeSelectedSource405 s q t e) :
    CompleteScopePriority405 trace := by
  exact SourceTrace.rec (R := authoredNativeSelectedSource405) (s := s)
    (motive_1 := fun _ _ _ trace => CompleteScopePriority405 trace)
    (motive_2 := fun _ _ deps => CompleteScopeWhere405 deps)
    (motive_3 := fun _ deps => CompleteScopeProducer405 deps)
    (fun _ => True.intro)
    (fun _ _ _ _ below => below)
    (fun e raw selected support kids before after =>
      ⟨authored_and_variable_rules_ground_the_same_trace405 raw selected support,before,after⟩)
    True.intro
    (fun _ _ one later => ⟨one,later⟩)
    True.intro
    (fun _ _ _ _ one later => ⟨one,later⟩)
    trace

/-- The integrated represented rules actually discharge priority for
every chosen node of this very source proof (including producer
dependencies). Its dictionary uses the same trace and ledger. No
claim about missing semantic cases or classification completeness. -/
theorem existing_source_rules_assemble_grounded_dictionary405 {s q t e d}
    (trace : SourceTrace authoredNativeSelectedSource405 s q t e)
    (chosen : Summarizes t (.selected d)) :
    CompleteScopePriority405 trace ∧
    ∃ tree : I72.GeneralTree trace d,
      CanonicalReplay tree tree.ledger ∧ LedgerMeaning Addresses tree.ledger ∧
      LedgerMeaning ExactSourceRhs tree.ledger ∧ ∀ m, Fits s m → DictionaryEvidence s m q d := by
  obtain ⟨tree,exact,meaning⟩ := authored_native_dictionary_reuses_given_trace405 trace chosen
  exact ⟨all_actual_selected_native_or_variable_nodes_have_priority405 trace,
    tree,exact,typed_replay_keeps_original_addresses _ s q t e d trace tree tree.ledger exact,
    draft_ledger_already_has_the_original_B6_RHS405 tree.ledger,meaning⟩

end Yulang.GeneralDeclarativeI65.I72
