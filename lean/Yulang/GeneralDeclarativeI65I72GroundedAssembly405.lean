import Yulang.GeneralDeclarativeI65I72GroundedPriority405

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72
open GeneralDeclarativeI65
open CommonRoleOutermostResolver (Dictionary Summarizes Tree)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)

/-- Substitute the actual candidate scan at the unique point the C402
dependency graph used the false universal S03. Downstream capture,
body and fixed-row premises are left in place. Neither old S03 nor a
different dictionary witness is needed at this call site. -/
theorem provide_node_from_grounded_priority405 {R : SourcePrimitives} (K : SourceSpecification R) :
    GroundedInversion405 R → S05 K → S06 K → S07 K → S08 K → S10 R := by
  intro invert capture ordinary typed makeNode s q e needs safe chosen support
  obtain ⟨actual⟩ := invert s q e needs safe chosen support
  let src := actual.toSelectedSource
  have same : SameAuthoredHead src e.head := ⟨actual.exactHead.symm,rfl⟩
  obtain ⟨binders,exact⟩ := capture s q e needs support src e.head same
  have literal : Nonempty (LiteralReceipt e) := by
    cases branch : K.bodyCase s q e with
    | ordinary => exact ordinary s q e needs support src e.head binders exact branch
    | typedOrMixed => exact typed s q e needs support src e.head binders exact branch
  obtain ⟨receipt⟩ := literal
  exact makeNode s q e needs support src e.head binders same exact receipt

/-- Conditional C402 assembly with unchanged dictionary quantifiers.
Its inversion assumption now asks for the actual scoped scan; it does
not claim that every production native candidate admits this slice. -/
theorem assemble_with_grounded_inversion405 {R : SourcePrimitives} (K : SourceSpecification R) :
    GroundedInversion405 R → S05 K → S06 K → S07 K → S08 K →
      S13bbba → S13bbbb → DictionarySound R := by
  intro invert capture ordinary typed makeNode rhs fixed
  exact assemble R (classifies_unpacks_source_in_signature R)
    (provide_node_from_grounded_priority405 K invert capture ordinary typed makeNode)
    (lower_selected_at_exact_trace R) (general_tree_meaning_from_local R semantic_node_in_signature)
    (typed_replay_alignment_in_signature R) (typed_replay_keeps_same_event_meaning R)
    (typed_replay_keeps_original_addresses R) rhs fixed

/-- Relative local proof attached to the exact selected trace; notably
the recursive output support remains the original separate forest,
rather than becoming a new request or set of sorted where children. -/
structure PriorityAt405 {R : SourcePrimitives} {s q} {e : Event s q} {needs}
    (support : SupportForest R s needs) : Prop where
  grounded : ∃ scan : GroundedSelection405 R e needs support,
    scan.scan.visits = [] ∧ scan.tape.waits = false ∧ scan.tape.live = [e.frame.decl] ∧
    scan.origin.rawOrdinal = e.frame.ordinal ∧ scan.origin.pick.head = e.head
  raw : ¬ RootCycle s q

theorem priority_at_actual_support405 {R} (invert : GroundedInversion405 R)
    {s q} (e : Event s q) (needs : List (OutputNeed s)) (support : SupportForest R s needs)
    (raw : ¬ RootCycle s q) (chosen : R.elected s q e needs) :
    PriorityAt405 (e := e) support := by
  obtain ⟨scan⟩ := invert s q e needs raw chosen support
  have priority := groundedS03_of_actual_variable_scan405 R s q e needs support scan raw chosen
  exact ⟨⟨scan,priority.2.1,priority.2.2.1,priority.2.2.2,scan.exactOrdinal,scan.exactHead⟩,raw⟩

mutual
def PrioritiesOnTree405 {R s q t e d} {trace : SourceTrace R s q t e} :
    I72.GeneralTree trace d → Prop
  | @GeneralTree.node _ _ _ _ _ _ event _ _ support _ _ children =>
    PriorityAt405 (e := event) support ∧ PrioritiesOnForest405 children

def PrioritiesOnForest405 {R s qs ts ds} {trace : WhereForest R s qs ts} :
    I72.GeneralForest trace ds → Prop
  | .nil => True
  | .cons a b => PrioritiesOnTree405 a ∧ PrioritiesOnForest405 b
end

theorem replay_checks_every_actual_selected_priority405 {R} (invert : GroundedInversion405 R)
    {s q t ev d} {trace : SourceTrace R s q t ev} (tree : I72.GeneralTree trace d) :
    PrioritiesOnTree405 tree := by
  exact I72.GeneralTree.rec (R := R) (s := s)
    (motive_1 := fun {_ _ _} _ _ node => PrioritiesOnTree405 node)
    (motive_2 := fun {_ _} _ _ children => PrioritiesOnForest405 children)
    (fun {q} {needs} {ts} {ds} {event} {safe} {rule} {support} {children} node forest rest =>
      ⟨priority_at_actual_support405 invert event needs support safe rule,rest⟩)
    True.intro
    (fun _ _ a b => ⟨a,b⟩)
    tree

/-- A single original selected witness provides same-state typed/body
readback and the retained target equality at the exact literal slot.
The fold's premises refer only to the actual C402 lowered tree, not all
arbitrary unbacked ledger values sharing its dictionary key. -/
theorem exact_ledger_evidence405 {s q d} (ledger : Ledger s q d) (m : Model) :
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

theorem fixed_targets_from_own_elected_events405 {R} (keeps : KeepsFixedOutputs404 R)
    {s q t ev d} {trace : SourceTrace R s q t ev} (tree : I72.GeneralTree trace d)
    (m : Model) (fit : Fits s m) :
    LedgerMeaning (FixedTargets m) tree.ledger := by
  exact I72.GeneralTree.rec (R := R) (s := s)
    (motive_1 := fun {_ _ _} _ _ node => LedgerMeaning (FixedTargets m) node.ledger)
    (motive_2 := fun {_ _} _ _ children => LedgerForestMeaning (FixedTargets m) children.ledger)
    (fun {q} {needs} {ts} {ds} {event} {safe} {rule} {support} {children} node forest rest => by
      change FixedTargets m event ∧ _
      exact ⟨(keeps s q event needs rule).elim
        (fun plain => retained_variable_targets_sound403 plain m fit)
        (fun typed => retained_typed_rows_satisfy_fixed_targets403 typed m fit),rest⟩)
    True.intro
    (fun _ _ a b => ⟨a,b⟩)
    tree

/-- The lexical center is read from the original grounded source head,
not reconstructed from equal endpoint values. This readback handles
both forms of the existing C365 head; it does not prove their coverage. -/
theorem node_from_exact_preoutput_head405 {s q} (e : Event s q)
    (checked : GeneralDeclarations.DeclarationChecked
      (authoredRegistry s.core.current).constructors (authoredRegistry s.core.current).roles e.frame.decl)
    (fallback : Nat → GeneralDeclarativeWhere319.Capture)
    (same : e.frame.input = preoutputInputOfHead399 e.head fallback) : GeneralNode e := by
  refine ⟨checked,?_⟩
  unfold CapturesActualHead
  cases form : e.head with
  | ordered input reads =>
    intro n inSource
    have lexical : e.frame.names.input n = e.frame.input n :=
      GeneralDeclarativeProducedNames325.exact_input checked inSource
    rw [lexical,same,form]
    rfl
  | joined observed =>
    intro n inSource
    have lexical : e.frame.names.input n = e.frame.input n :=
      GeneralDeclarativeProducedNames325.exact_input checked inSource
    rw [lexical,same,form]
    change (joinedPreoutputInput399 observed fallback n).center = observed.actualValue
    rw [joined_original_payload_capture399 observed fallback inSource]
    rfl

theorem actual_completed_choices_supply_nodes405 : S10 completedChoiceSource404 := by
  intro s q e needs raw rule support
  rcases rule with old|new
  · obtain ⟨read⟩ := old.2.1
    have checked := read.elected.scope.checked.2 e.frame.decl (List.mem_of_getElem? e.frame.authored)
    refine node_from_exact_preoutput_head405 e checked (fun _ => emptyCapture403) ?_
    rw [read.sameHead]
    exact congrArg AuthoredBodyFrame393.input read.sameFrame
  · obtain ⟨read⟩ := new.1
    have checked := read.choice.checked.2 e.frame.decl (List.mem_of_getElem? e.frame.authored)
    refine node_from_exact_preoutput_head405 e checked (fun _ => emptyCapture403) ?_
    rw [read.head]
    exact congrArg AuthoredBodyFrame393.input read.frame

/-- Concrete rule instantiation of repaired inversion and the
same-state dictionary fold. Every node in the returned original
ordered tree carries a grounded scan. Models are introduced only
after its literal ledger, addresses and priorities are fixed. -/
theorem completed_choice_same_priority_and_ledger405 {s q d}
    (chosen : Classifies completedChoiceSource404 s q (.selected d)) :
    ∃ (t : Tree) (ev : Option (Event s q)) (trace : SourceTrace completedChoiceSource404 s q t ev)
        (tree : I72.GeneralTree trace d) (ledger : Ledger s q d),
      Summarizes t (.selected d) ∧ PrioritiesOnTree405 tree ∧ CanonicalReplay tree ledger ∧
      LedgerMeaning Addresses ledger ∧ ∀ m, Fits s m →
        LedgerMeaning (LocalMeaning m) ledger ∧ LedgerMeaning (FixedTargets m) ledger ∧
          DictionaryEvidence s m q d := by
  obtain ⟨t,_,source,summary⟩ := classifies_unpacks_source_in_signature _ s q d chosen
  obtain ⟨⟨tree⟩,rendered⟩ := (lower_selected_at_exact_trace _ s
    (actual_completed_choices_supply_nodes405 s)).tree source.source summary
  obtain ⟨ledger,aligned⟩ := typed_replay_alignment_in_signature _ s q t source.event d source.source tree rendered
  refine ⟨t,source.event,source.source,tree,ledger,summary,
    replay_checks_every_actual_selected_priority405 actual_completed_choice_grounds_visits405 tree,
    aligned,typed_replay_keeps_original_addresses _ s q t source.event d source.source tree ledger aligned,?_⟩
  intro m fit
  have body := typed_replay_keeps_same_event_meaning _ s q t source.event d source.source tree ledger m aligned
    (general_tree_meaning_from_local _ semantic_node_in_signature s q t source.event d source.source tree m fit)
  have fixed : LedgerMeaning (FixedTargets m) ledger := by
    rw [← aligned.1]
    exact fixed_targets_from_own_elected_events405 completed_choice_keeps_fixed_rows404 tree m fit
  exact ⟨body,fixed,exact_ledger_evidence405 ledger m body fixed⟩

end Yulang.GeneralDeclarativeI65.I72
