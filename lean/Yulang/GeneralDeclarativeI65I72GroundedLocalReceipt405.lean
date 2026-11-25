import Yulang.GeneralDeclarativeI65I72GroundedPositions405

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72
open GeneralDeclarativeI65
open GeneralDeclarations (Declaration Clause Checked)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarationPatterns (Pattern)
open GeneralDeclarativeEqualities322 (Derives)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)

private theorem retained_span_reaches_first_center405 {s : State} {q d}
    (row : RepeatedRow403 q d)
    (retained : ∀ eq ∈ selectedCenterRows403 q row, eq ∈ s.core.current.ordinary.equations)
    {name a} (seen : (name,a) ∈ selectedInputSpans403 q row) :
    Derives s.core.current.ordinary (.variable a.center)
      (.variable (selectedInput403 q row name).center) := by
  by_cases same : a.center = (selectedInput403 q row name).center
  · rw [same]
    exact .refl _
  · exact .row (retained _ ((binder_center_batch_exact403 row).mpr ⟨name,a,seen,same,rfl⟩))

private theorem retained_scoped_spans_are_tied405 {s : State} {q d} (row : RepeatedRow403 q d)
    (retained : ∀ eq ∈ selectedCenterRows403 q row, eq ∈ s.core.current.ordinary.equations) :
    ∀ n a b, (n,a) ∈ selectedInputSpans403 q row → (n,b) ∈ selectedInputSpans403 q row →
      Derives s.core.current.ordinary (.variable a.center) (.variable b.center) :=
  fun _ _ _ left right => .trans (retained_span_reaches_first_center405 row retained left)
    (.symm (retained_span_reaches_first_center405 row retained right))

/-- No fixed target premise is used to identify which literal body
or typed RHS was supplied at this occurrence. The retained target
obligation is still separate, as in the C402 meaning. -/
theorem candidate_keeps_original_B6_body405 {s q} (e : Event s q) : ExactSourceRhs e :=
  fun i => ⟨(e.outputs i).supplied,(e.outputs i).originalTyped,(e.outputs i).formed⟩

/-- This is a local receipt of the current represented rule, not a
new condition for Classifies. It is constructed from the chosen
data and the given strictly smaller proof, before reading Fits. -/
structure GroundedLocalReceipt405 {s q} (e : Event s q) {needs}
    (support : SupportForest completedChoiceSource404 s needs) where
  observed : GroundedSelection405 completedChoiceSource404 e needs support
  priority : ¬RootCycle s q ∧ observed.scan.visits = [] ∧ observed.tape.waits = false ∧
    observed.tape.live = [e.frame.decl]
  originalRow : RepeatedRow403 q e.frame.decl
  capture : GeneralCapture e e.head
  exactSpans : capture.spans = selectedInputSpans403 q originalRow
  exactNames : capture.names = e.frame.names.input
  exactCenter : CapturesActualHead e
  tied : TieRows capture
  receipt : LiteralReceipt e
  whereExact : ∀ i (clause : Clause), e.frame.decl.requirements[i]? = some clause →
    ∃ binders : List Nat, clause.arguments = binders.map Pattern.var ∧
      receipt.kids[i]? = some (⟨q.occurrence ++ [i],⟨clause.role,binders.map e.frame.input,[]⟩⟩ : Request)
  rhs : ExactSourceRhs e

private def grounded_scoped_local_receipt405 {s q e needs support}
    (observed : GroundedSelection405 (s := s) (q := q) completedChoiceSource404 e needs support)
    (raw : ¬RootCycle s q) (row : RepeatedRow403 q e.frame.decl)
    (captured : CapturesActualHead e)
    (scope : LiteralVariableWhere403 e.frame.decl)
    (checked : Checked (authoredRegistry s.core.current))
    (retained : ∀ eq ∈ selectedCenterRows403 q row, eq ∈ s.core.current.ordinary.equations) :
    GroundedLocalReceipt405 e support :=
  ⟨observed,grounded_selected_priority405 observed raw,row,
    ⟨selectedInputSpans403 q row,e.frame.names.input⟩,rfl,rfl,captured,
    retained_scoped_spans_are_tied405 row retained,
    ⟨List.ofFn (fun i => (e.outputs i).receipt),e.kids,rfl,rfl⟩,
    fun _ _ seen => literal_where_child_at403 e.frame scope checked seen,
    candidate_keeps_original_B6_body405 e⟩

/-- The original selected rule fixes every argument and binder in
sequence. The center equalities are facts read after selection,
not inputs of head comparison. The same witness includes literal
where kids and the B6 receipt order. -/
theorem actual_selection_derives_grounded_local_receipt405
    {s q e needs} (raw : ¬ RootCycle s q) (rule : completedChoiceSource404.elected s q e needs)
    (support : SupportForest completedChoiceSource404 s needs) :
    Nonempty (GroundedLocalReceipt405 e support) := by
  have captures := (actual_completed_choices_supply_nodes405 s q e needs raw rule support).captures
  rcases rule with old|new
  · obtain ⟨source⟩ := old.2.1
    let scan : GroundedSelection405 completedChoiceSource404 e needs support :=
      ⟨selectedRepeatedTape403 source.elected source.retained,source.origin,
        (congrArg AuthoredBodyFrame393.ordinal source.sameFrame).symm,source.sameHead.symm,
        single_variable_scan405 _ source.elected.sole
          (selectedRepeatedCandidate403 source.elected source.retained) source.elected.row,source.elected.sole⟩
    exact ⟨grounded_scoped_local_receipt405 scan raw source.elected.row captures source.sourceClauses source.elected.scope.checked source.retained⟩
  · obtain ⟨source⟩ := new.1
    let scan : GroundedSelection405 completedChoiceSource404 e needs support :=
      ⟨supportedTape404 source.choice source.retained,source.origin,
        (congrArg AuthoredBodyFrame393.ordinal source.frame).symm,source.head.symm,
        single_variable_scan405 _ source.choice.sole
          (supportedCandidate404 source.choice source.retained) source.choice.row,source.choice.sole⟩
    exact ⟨grounded_scoped_local_receipt405 scan raw source.choice.row captures source.sourceClauses source.choice.checked source.retained⟩

theorem grounded_receipt_reads_literal_where_and_every_output405
    {s q e needs support} (localRead : GroundedLocalReceipt405 (s := s) (q := q) e (needs := needs) support) :
    (∀ i (clause : Clause), e.frame.decl.requirements[i]? = some clause →
      ∃ binders : List Nat, clause.arguments = binders.map Pattern.var ∧
        e.kids[i]? = some (⟨q.occurrence ++ [i],⟨clause.role,binders.map e.frame.input,[]⟩⟩ : Request)) ∧
    ∀ i : Fin q.demand.outputs.length,
      localRead.receipt.written[i.val]? = some (e.outputs i).receipt ∧
      (e.outputs i).receipt.original.target = q.demand.outputs[i].target ∧
      (e.outputs i).receipt.occurrence = q.occurrence ∧
      (e.outputs i).receipt.outputOrdinal = i.val := by
  refine ⟨?_,?_⟩
  · intro i clause written
    have child := localRead.whereExact i clause written
    rwa [localRead.receipt.sameWhere] at child
  · intro i
    rw [localRead.receipt.sameOutput,List.getElem?_ofFn,dite_eq_left i.isLt]
    exact ⟨rfl,rfl,rfl,rfl⟩

end Yulang.GeneralDeclarativeI65.I72
