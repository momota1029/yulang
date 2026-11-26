import Yulang.GeneralDeclarativeI65I74StructuralWhereRule431

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.StructuralWhere431
open GeneralDeclarativeI65 StructuralWhere427 StructuralWhere428
open CommonRoleOutermostResolver (Tree Dictionary Summarizes)
open Checker408 (Problem Result)

structure Wire where
  selected : PositivePairWire427
  parentVisits : ExactRecordVisitWire427
  childVisits : ExactRecordVisitWire427

/-- The supplied data identifies original graph/declaration positions
and finite raw visits only. No picked Event, child Request, or output
dictionary is read from the wire. -/
def readOriginal (p : Problem) (w : Wire) : Option (ActualPair p.state p.root) := do
  let a ← readOriginalPositivePair427 p.state.core p.root w.selected
  if ok : checkWholePairRawVisits427 a w.parentVisits w.childVisits = true then
    let raw := whole_pair_preserves_original_raw_K2_for_both_complete_candidate_lists427 ok
    pure ⟨a,raw.1,raw.2⟩
  else none

theorem OriginalWhereFromSource431 {s q} (a : ActualPair s q) :
    a.parent.kids = [a.pair.original.child] ∧
    a.pair.original.child.occurrence = q.occurrence ++ [0] ∧
    s.core.current.ordinary.equations[a.pair.original.rowOrdinal]? =
      some (writtenRow427 a.pair.frame a.pair.original.name
        a.pair.original.label a.pair.original.binder) :=
  ⟨one_structural_where_has_exact_original_child427 a.pair.original a.pair.rootHasOneWhere,
    rfl,a.pair.original.retained⟩

def ActualPair.childTree {s q} (a : ActualPair s q) : Tree :=
  .selected a.pair.childFrame.decl.id []

def ActualPair.tree {s q} (a : ActualPair s q) : Tree :=
  .selected a.pair.frame.decl.id [a.childTree]

def ActualPair.dictionary {s q} (a : ActualPair s q) : Dictionary :=
  .node a.pair.frame.decl.id [.node a.pair.childFrame.decl.id []]

def ActualPair.report {s q} (a : ActualPair s q) : Result :=
  ⟨a.tree,.selected a.dictionary,[]⟩

theorem child_picked431 {s q} (a : ActualPair s q) :
    R15.named426.elected s a.pair.original.child a.child [] :=
  .inr ⟨rfl,⟨.child a⟩⟩

theorem parent_picked431 {s q} (a : ActualPair s q) :
    R15.named426.elected s q a.parent [] :=
  .inr ⟨rfl,⟨.parent a⟩⟩

theorem leaf_kids431 {s q} (a : ActualPair s q) : a.child.kids = [] := by
  simp [ActualPair.child,originalNoOutputEvent427,Event.kids,frameWhereKids400,
    AuthoredBodyFrame393.clauses,a.pair.childHasNoWhere,children]

def childTrace431 {s q} (a : ActualPair s q) :
    SourceTrace R15.named426 s a.pair.original.child a.childTree (some a.child) :=
  .selected a.child (a.pair.child.safe s.b6) (child_picked431 a) .nil
    ((leaf_kids431 a).symm ▸ (.nil : WhereForest R15.named426 s [] []))

def sourceForest431 {s q} (a : ActualPair s q) :
    WhereForest R15.named426 s [a.pair.original.child] [a.childTree] :=
  .cons (childTrace431 a) .nil

def actualSourceTrace431 {s q} (a : ActualPair s q) :
    SourceTrace R15.named426 s q a.tree (some a.parent) :=
  .selected a.parent (a.pair.root.safe s.b6) (parent_picked431 a) .nil
    ((OriginalWhereFromSource431 a).1.symm ▸ sourceForest431 a)

private theorem selected_survives_child_request_equality431
    {s : I72.State} {qs us ts} {q : Request} {e : Event s q} {i : Nat}
    (same : qs = us) (forest : WhereForest R15.named426 s qs ts)
    (actual : SelectedAt428 R15.named426 s forest i q e) :
    SelectedAt428 R15.named426 s (same ▸ forest) i q e := by
  cases same
  exact actual

theorem selected_trace_keeps_real_child_event431 {s q} (a : ActualPair s q) :
    TraceChild428 (actualSourceTrace431 a) 0 a.pair.original.child a.child :=
  selected_survives_child_request_equality431 (OriginalWhereFromSource431 a).1.symm
    (sourceForest431 a) (.here (childTrace431 a) .nil)

theorem real_raw_root_cycle_never_selects_R15_431 {s q} (cycle : RootCycle s q) (d : Dictionary) :
    ¬ Classifies R15 s q (.selected d) :=
  I72.root_k2_never_selects (R := R15) cycle

theorem actual_tree_has_no_support_or_writes431 {s q} (a : ActualPair s q) :
    ZeroSupportSelected428 (actualSourceTrace431 a) ∧
    namedTraceWrites428 (actualSourceTrace431 a) = [] := by
  have child : ZeroSupportSelected428 (childTrace431 a) :=
    selected_leaf_with_zero_outputs_and_no_where_has_no_support428 a.child
      (a.pair.child.safe s.b6) (child_picked431 a) (leaf_kids431 a) a.pair.childNoOutput
  have zero : ZeroSupportSelected428 (actualSourceTrace431 a) :=
    ⟨rfl,a.pair.rootNoOutput,no_support_where_cast428
      (OriginalWhereFromSource431 a).1.symm (sourceForest431 a) ⟨child,True.intro⟩⟩
  exact ⟨zero,support_free_original_named_trace_encodes_no_writes428 _ zero⟩

theorem exact_original_tree_summary431 {s q} (a : ActualPair s q) :
    Summarizes a.tree a.report.verdict :=
  .selected (.cons (.selected .nil (.selected rfl)) .nil) (.selected rfl)

theorem exact_original_report_classifies431 {s q} (a : ActualPair s q) :
    Classifies R15 s q a.report.verdict :=
  legacy_classification_included426 ⟨a.tree,some a.parent,⟨actualSourceTrace431 a⟩,
    exact_original_tree_summary431 a⟩

def ClassifiedAs (s : I72.State) (q : Request) (r : Result) : Prop :=
  EndpointProjection426.ClassifiedAs s q r ∨
    ∃ a : ActualPair s q, r = a.report ∧ r.writes = namedTraceWrites428 (actualSourceTrace431 a)

def ReportEvidence (s : I72.State) (m : I72.Model) (q : Request) (r : Result) : Prop :=
  EndpointProjection426.ReportEvidence s m q r ∨
    ∃ a : ActualPair s q, r = a.report ∧ DictionaryEvidence s m q a.dictionary

inductive Witness where
  | previous (w : EndpointProjection426.Witness)
  | originalStructuralWhere (w : Wire)
  | unsupported

def check (p : Problem) (r : Result) : Witness → Bool
  | .previous w => EndpointProjection426.check p r w
  | .originalStructuralWhere w => match readOriginal p w with
    | none => false
    | some a => Check408.matchesNoWrites r a.report.tree a.report.verdict
  | .unsupported => false

theorem previous_entry_is_identical431 (p : Problem) (r : Result) (w : EndpointProjection426.Witness) :
    check p r (.previous w) = EndpointProjection426.check p r w := rfl

theorem executable_report_is_original431 (p : Problem) (r : Result) (w : Wire)
    (ok : check p r (.originalStructuralWhere w) = true) :
    ∃ a, readOriginal p w = some a ∧ r = a.report := by
  cases h : readOriginal p w with
  | none => simp [check,h] at ok
  | some a =>
    have same : Check408.matchesNoWrites r a.report.tree a.report.verdict = true := by
      simpa [check,h] using ok
    obtain ⟨tree,verdict,writes⟩ := Check408.matchesNoWrites_exact408.mp same
    refine ⟨a,rfl,?_⟩
    cases r
    simp only at tree verdict writes
    subst_vars
    rfl

theorem check_sound (p : Problem) (r : Result) (w : Witness) (good : check p r w = true) :
    ClassifiedAs p.state p.root r ∧
      ∀ m : I72.Model, Fits p.state m → ReportEvidence p.state m p.root r := by
  cases w with
  | previous w =>
    obtain ⟨before,meaning⟩ := EndpointProjection426.check_sound p r w good
    exact ⟨.inl before,fun m fit => .inl (meaning m fit)⟩
  | originalStructuralWhere w =>
    obtain ⟨a,_,same⟩ := executable_report_is_original431 p r w good
    subst r
    exact ⟨.inr ⟨a,rfl,(actual_tree_has_no_support_or_writes431 a).2.symm⟩,
      fun m fit => .inr ⟨a,rfl,dictionary_sound_R15 _ _ _ (exact_original_report_classifies431 a) m fit⟩⟩
  | unsupported => simp [check] at good

theorem verified_R15_result_classifies_in_same_State431 (p : Problem) (r : Result)
    (w : Witness) (good : check p r w = true) :
    Classifies R15 p.state p.root r.verdict ∧
      ∀ m : I72.Model, Fits p.state m → ReportEvidence p.state m p.root r := by
  obtain ⟨classified,meaning⟩ := check_sound p r w good
  refine ⟨?_,meaning⟩
  rcases classified with before|⟨a,rfl,_⟩
  · exact legacy_R14_classification_included431
      (EndpointProjection426.exact_projected_and_legacy_reports_classify_R14_426 before)
  · exact exact_original_report_classifies431 a

end Yulang.GeneralDeclarativeI65.I72.StructuralWhere431
