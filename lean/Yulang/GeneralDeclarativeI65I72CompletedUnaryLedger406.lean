import Yulang.GeneralDeclarativeI65I72CompletedUnaryTrace406

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72
open GeneralDeclarativeI65
open CommonRoleOutermostResolver (All₂ Dictionary Result Tree Summarizes)
open GeneralDeclarativeWitnessTree349 (dictionaryForest)

theorem actual_prior_where_keeps_grounded_priority406 {s qs ts}
    (before : WhereForest PriorSource406 s qs ts) : CompleteScopeWhere405 before := by
  cases before with
  | nil => exact True.intro
  | cons first later =>
    exact ⟨all_actual_selected_native_or_variable_nodes_have_priority405 first,
      actual_prior_where_keeps_grounded_priority406 later⟩
termination_by structural before

theorem actual_prior_support_keeps_grounded_priority406 {s needs}
    (before : SupportForest PriorSource406 s needs) : CompleteScopeProducer405 before := by
  cases before with
  | nil => exact True.intro
  | cons first _ _ later =>
    exact ⟨all_actual_selected_native_or_variable_nodes_have_priority405 first,
      actual_prior_support_keeps_grounded_priority406 later⟩
termination_by structural before

/-- Lower the old exact ordered where forest with the actual old
source rules and same State. Its proof-level origins do not become
children of the dictionary merely because a head depended on them. -/
theorem prior_where_dictionary_uses_one_model406 {s qs ts ds}
    {given : WhereForest PriorSource406 s qs ts}
    (whereTree : I72.GeneralForest given ds) (m : Model) (fit : Fits s m) :
    DictionaryEvidenceForest s m qs ds := by
  exact I72.GeneralForest.rec (R := PriorSource406) (s := s)
    (motive_1 := fun {q _ _} _ d _ => DictionaryEvidence s m q d)
    (motive_2 := fun {qs _} _ ds _ => DictionaryEvidenceForest s m qs ds)
    (fun {q} {needs} {ts} {ds} {event} {raw} {rule} {support} {kids} node _ below => by
      have retained := authored_native_source_keeps_own_fixed_rows405 s q event needs rule
      exact .node event (semantic_node_in_signature s q event node m fit)
        (retained.elim (fun plain => retained_variable_targets_sound403 plain m fit)
          (fun typed => retained_typed_rows_satisfy_fixed_targets403 typed m fit)) below)
    .nil
    (fun _ _ first later => .cons first later)
    whereTree

/-- Evidence keeps the prior C405 branch unchanged. For the new root,
its semantic access to the B6 fixed lower, independent authored upper
and original path is explicit, and its children use the original
C405 dictionary evidence in the same model. -/
inductive ScopedEvidence406 (s : State) (m : Model) : Request → Dictionary → Prop where
  | prior : DictionaryEvidence s m q d → ScopedEvidence406 s m q d
  | completed (event : CompletedInvocation406 s q trees) :
      CompletedInvocationMeaning406 event m → DictionaryEvidenceForest s m event.kids ds →
      ScopedEvidence406 s m q (.node event.row.id ds)

inductive ScopedLedger406 (s : State) : Request → Dictionary → Type where
  | prior : Ledger s q d → ScopedLedger406 s q d
  | completed (event : CompletedInvocation406 s q trees) :
      I72.GeneralForest event.children ds → ScopedLedger406 s q (.node event.row.id ds)

def ScopedLedger406.written {s q d} (ledger : ScopedLedger406 s q d) : List (NamedMixedReceipt401 s.core) :=
  match ledger with
  | .prior old => old.written
  | .completed event whereTree => event.body.written ++ whereTree.ledger.written

def ScopedLedger406.visitRoot {s q d} (ledger : ScopedLedger406 s q d) : Option (List CandidateVisit) :=
  match ledger with
  | .prior _ => none
  | .completed event _ => some event.visits

def ScopedLedger406.Means {s q d} (ledger : ScopedLedger406 s q d) (m : Model) : Prop :=
  match ledger with
  | .prior old =>
    LedgerMeaning (LocalMeaning m) old ∧ LedgerMeaning (FixedTargets m) old
  | @ScopedLedger406.completed _ _ _ ds event _ =>
    CompletedInvocationMeaning406 event m ∧ DictionaryEvidenceForest s m event.kids ds

theorem same_ledger_yields_scoped_evidence406 {s q d} (ledger : ScopedLedger406 s q d) (m : Model) :
    ledger.Means m → ScopedEvidence406 s m q d := by
  cases ledger with
  | prior old =>
    intro h
    exact .prior (exact_ledger_evidence405 old m h.1 h.2)
  | completed event tree =>
    intro h
    exact .completed event h.1 h.2

/-- Both old and new branches construct a single trace-indexed ledger
before any model is introduced. The new nonempty visit list stays
attached to the exact new frame in that trace. -/
def GroundedReplayOn406 {s q t d} (source : ScopedSource406 s q t)
    (ledger : ScopedLedger406 s q d) : Prop :=
  match source with
  | .prior trace => ∃ tree : I72.GeneralTree trace d,
      ledger = .prior tree.ledger ∧ CompleteScopePriority405 trace ∧
      CanonicalReplay tree tree.ledger
  | .completed event => ∃ (ds : List Dictionary) (whereTree : I72.GeneralForest event.children ds),
      ∃ matchID : Dictionary.node event.row.id ds = d,
        ledger = matchID ▸ (.completed event whereTree) ∧
        CompleteScopeProducer405 event.forest ∧ CompleteScopeWhere405 event.children ∧
        (∀ step ∈ event.visits, step.declarationOrdinal = event.frame.ordinal ∧ ¬CurrentCycleAt s step.site)

theorem actual_scoped_trace_assembles_one_ledger406 {s q t d} (trace : ScopedSource406 s q t)
    (selected : Summarizes t (.selected d)) :
    ∃ ledger : ScopedLedger406 s q d, GroundedReplayOn406 trace ledger ∧
      ∀ m, Fits s m → ledger.Means m ∧ ScopedEvidence406 s m q d := by
  cases trace with
  | prior old =>
    obtain ⟨priority,tree,exact,_,_,_⟩ := existing_source_rules_assemble_grounded_dictionary405 old selected
    refine ⟨.prior tree.ledger,⟨tree,rfl,priority,exact⟩,fun m fit => ?_⟩
    have localMeaning := typed_replay_keeps_same_event_meaning _ s q t _ d old tree tree.ledger m exact
      (general_tree_meaning_from_local _ semantic_node_in_signature s q t _ d old tree m fit)
    have fixed := fixed_targets_from_own_elected_events405 authored_native_source_keeps_own_fixed_rows405 tree m fit
    exact ⟨⟨localMeaning,fixed⟩,.prior (exact_ledger_evidence405 tree.ledger m localMeaning fixed)⟩
  | completed event =>
    cases selected with
    | selected childSummaries combine =>
      cases combine with
      | selected eq =>
        rw [eq] at childSummaries
        obtain ⟨⟨whereTree⟩,_⟩ := (lower_selected_at_exact_trace _ s
          (authored_native_source_provides_nodes405 s)).forest event.children childSummaries
        refine ⟨.completed event whereTree,⟨_,whereTree,rfl,rfl,
          actual_prior_support_keeps_grounded_priority406 event.forest,
          actual_prior_where_keeps_grounded_priority406 event.children,
          (completed_root_never_inspects_variable_payload406 event.chosen).1⟩,fun m fit => ?_⟩
        have meaning := completed_invocation_means_one_state_and_model406 event m fit
        have child := prior_where_dictionary_uses_one_model406 whereTree m fit
        exact ⟨⟨meaning,child⟩,.completed event meaning child⟩

/-- Same I-65 quantifier structure for this scoped representation.
This does not close the frozen integration theorem or assert coverage
for arbitrary positive/native source forms. -/
theorem scoped_dictionary_sound406 :
    ∀ s q d, ScopedClassifies406 s q (.selected d) → ∀ m, Fits s m → ScopedEvidence406 s m q d := by
  rintro s q d ⟨t,⟨trace⟩,selected⟩ m fit
  obtain ⟨_,_,whole⟩ := actual_scoped_trace_assembles_one_ledger406 trace selected
  exact (whole m fit).2

end Yulang.GeneralDeclarativeI65.I72
