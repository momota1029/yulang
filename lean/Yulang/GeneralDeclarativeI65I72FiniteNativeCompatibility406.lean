import Yulang.GeneralDeclarativeI65I72CompletedNativeSourceIndex406

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72
open GeneralDeclarativeI65
open CommonRoleOutermostResolver (All₂ Tree Dictionary Result Summarizes)
open GeneralDeclarations (Declaration)

def PreselectedUnary406.exactFiniteProducer {s q row needs forest}
    (chosen : PreselectedUnary406 s q row (needs := needs) forest) :
    FiniteNative406 s chosen.need.producer chosen.need.dictionary
      (fun i => (chosen.producer.event.outputs i).receipt) :=
  .base (.prior chosen.producer.source) chosen.producer.completion
    (fun i => .prior (i := i) chosen.producer.source)

theorem PrereadAt406_same_need_with_actual_receipt {s q row needs forest}
    (chosen : PreselectedUnary406 s q row (needs := needs) forest) :
    (⟨chosen.need.producer,chosen.need.dictionary,chosen.need.ordinal,
      (chosen.producer.event.outputs chosen.need.ordinal).receipt⟩ : OutputNeed s) = chosen.need :=
  congrArg (fun receipt => (⟨chosen.need.producer,chosen.need.dictionary,chosen.need.ordinal,receipt⟩ : OutputNeed s))
    chosen.producer.sameTypedOutput

private theorem exact_step_need_transport_keeps_its_payload406 {s q a b trees} (same : a = b)
    (step : FiniteUnaryStep406 s q a trees) :
    let ext : FiniteUnaryStep406 s q b trees := same ▸ step
    ext.row = step.row ∧ ext.frame = step.frame ∧ ext.written = step.written ∧
      ext.head.visits = step.head.visits ∧ HEq ext.kids step.kids := by
  cases same
  exact ⟨rfl,rfl,rfl,rfl,HEq.rfl⟩

/-- Compare the *same* original C406 positive invocation with a
literal advance in the finite dependency calculus. No earlier
trace is found by search. Its exact where list, actual frame,
visits and B6 receipts are unchanged; only the proof index is cast
along the already established typed output identity. -/
theorem exact_completed_root_is_one_original_finite_step406 {s q trees} {ds : List Dictionary}
    (event : CompletedInvocation406 s q trees)
    (selectedKids : All₂ Summarizes trees (ds.map Result.selected)) :
    let chosen := event.chosen
    ∃ ext : FiniteUnaryStep406 s q
      ⟨chosen.need.producer,chosen.need.dictionary,chosen.need.ordinal,
        (chosen.producer.event.outputs chosen.need.ordinal).receipt⟩ trees,
      ext.row = event.row ∧ ext.frame = event.frame ∧ ext.written = event.body.written ∧
      ext.head.visits = event.visits ∧ HEq ext.kids event.children ∧
      ∃ ledger : FiniteNativeLedger406 s (.advance chosen.exactFiniteProducer ext selectedKids),
        ∀ m, Fits s m → ledger.Means m := by
  let chosen := event.chosen
  let equal := (PrereadAt406_same_need_with_actual_receipt chosen).symm
  let ext : FiniteUnaryStep406 s q
    ⟨chosen.need.producer,chosen.need.dictionary,chosen.need.ordinal,
      (chosen.producer.event.outputs chosen.need.ordinal).receipt⟩ trees :=
    equal ▸ event.liftStep
  have ⟨row,frame,written,visits,kids⟩ := exact_step_need_transport_keeps_its_payload406 equal event.liftStep
  exact ⟨ext,row,frame,written,visits,kids,
    (finite_completed_native_source_assembles_exact_ledger406
      (.advance chosen.exactFiniteProducer ext selectedKids)).2⟩

theorem finite_step_writes_output_and_where_but_not_dependency406 {s q p d original trees ds}
    {producer : FiniteNative406 s p d original} {i : Fin p.demand.outputs.length}
    (step : FiniteUnaryStep406 s q ⟨p,d,i,original i⟩ trees)
    (done : All₂ Summarizes trees (ds.map Result.selected))
    (prior : FiniteNativeLedger406 s producer) (whereTree : I72.GeneralForest step.kids ds) :
    (FiniteNativeLedger406.advance (whereDone := done) prior whereTree).written =
      step.written ++ whereTree.ledger.written := rfl

/-- Two exact completed-lower proofs of the same request might use
different finite producers. The visited root still has the same
original declaration position and argument address. No semantic
equality of producer values is assumed or used. -/
theorem original_native_visit_list_independent_of_producer406
    {s q leftRow rightRow ls rs lf rf}
    (left : PreselectedUnary406 s q leftRow (needs := ls) lf)
    (right : PreselectedUnary406 s q rightRow (needs := rs) rf) :
    leftRow = rightRow ∧ left.visits = right.visits := by
  have declared := List.cons.inj (left.gate.only.symm.trans right.gate.only) |>.1
  have arg := List.cons.inj (left.gate.exactArg.symm.trans right.gate.exactArg) |>.1
  have address := Option.some.inj (left.exactOrdinal.symm.trans right.exactOrdinal)
  exact ⟨declared,by simp [PreselectedUnary406.visits,arg,address]⟩

/-- A genuine guard can succeed while this proof representation has
no annotated original-name readback. In this situation the shadow
extension contributes no result, rather than incorrectly changing
that guard into delay/rejection or selecting a fabricated center. -/
theorem no_exact_original_name_keeps_prior_verdict_only406 {s q result}
    (missing : ∀ arg ∈ q.demand.arguments, ∀ o ∈ s.core.origins, ¬OriginRoute s.core o arg.center) :
    ScopedClassifies406 s q result ↔ Classifies PriorSource406 s q result := by
  constructor
  · rintro ⟨t,⟨trace⟩,summary⟩
    cases trace with
    | prior original => exact ⟨t,_,⟨original⟩,summary⟩
    | completed e =>
      have argument : e.chosen.gate.arg ∈ q.demand.arguments := by simp [e.chosen.gate.exactArg]
      exact (missing e.chosen.gate.arg argument e.actualPayload.source e.actualPayload.authored
        e.actualPayload.originalRoute).elim
  · exact previous_classification_embeds406

theorem can_compare_before_missing_original_name_remains_unresolved406 {s q row needs need}
    (gate : CompletedUnaryGate406 s q row need)
    (forest : SupportForest PriorSource406 s needs) (n : Nat) (atN : needs[n]? = some need)
    (safe : ¬RootCycle s q)
    (absent : ∀ o : Origin, o ∈ s.core.origins → ¬OriginRoute s.core o gate.arg.center) :
    ∃ selected : PreselectedUnary406 s q row forest,
      selected.gate.arg = gate.arg ∧ ¬Nonempty (OriginalPayload406 selected) := by
  have order : (visible s.core q)[0]? = some row := by simp [gate.only]
  obtain ⟨j,raw,authored⟩ := unfilterOrdinal395_exact _
    (GeneralDeclarativeWitnessDeclaredState357.authoredRegistry s.core.current).declarations 0 order
  let selected : PreselectedUnary406 s q row forest := ⟨need,n,atN,gate,safe,j,raw,authored⟩
  exact ⟨selected,rfl,missing_original_input_prevents_this_readback_only406 selected absent⟩

end Yulang.GeneralDeclarativeI65.I72
