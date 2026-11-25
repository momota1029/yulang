import Yulang.GeneralDeclarativeI65I72GroundedRawOrder405

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72
open GeneralDeclarativeI65
open CommonRoleOutermostResolver (Dictionary Result Summarizes Tree All₂)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarations (Declaration Checked)
open GeneralDeclarationPatterns (Pattern)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarativeWitnessModeCoverage357 (DeclarationCovered)

/-- Stronger replay for a *given* concrete source proof, not extraction
of some proof from the existential Classifies proposition. This
keeps both its selected event and its actual dependency choices. -/
theorem assemble_at_given_original_trace405 {s q t ev d}
    (trace : SourceTrace completedChoiceSource404 s q t ev) (done : Summarizes t (.selected d)) :
    ∃ tree : I72.GeneralTree trace d,
      TracePriority405 trace ∧ PrioritiesOnTree405 tree ∧ CanonicalReplay tree tree.ledger ∧
      LedgerMeaning Addresses tree.ledger ∧ LedgerMeaning ExactSourceRhs tree.ledger ∧
      ∀ m, Fits s m → DictionaryEvidence s m q d := by
  obtain ⟨⟨tree⟩,shape⟩ := (lower_selected_at_exact_trace _ s
    (actual_completed_choices_supply_nodes405 s)).tree trace done
  have matchExact : CanonicalReplay tree tree.ledger := ⟨rfl,shape,rfl⟩
  refine ⟨tree,
    every_entered_selected_proof_keeps_grounded_priority405 actual_completed_choice_grounds_visits405 trace,
    replay_checks_every_actual_selected_priority405 actual_completed_choice_grounds_visits405 tree,
    matchExact,typed_replay_keeps_original_addresses _ s q t ev d trace tree tree.ledger matchExact,
    draft_ledger_already_has_the_original_B6_RHS405 tree.ledger,?_⟩
  intro m fit
  have semantic := typed_replay_keeps_same_event_meaning _ s q t ev d trace tree tree.ledger m matchExact
    (general_tree_meaning_from_local _ semantic_node_in_signature s q t ev d trace tree m fit)
  exact exact_ledger_evidence405 tree.ledger m semantic
    (fixed_targets_from_own_elected_events405 completed_choice_keeps_fixed_rows404 tree m fit)

/-- Build the chosen event on top of the *same* input-support forest.
The lexical B6 output derivations and ordered where derivations remain
original and are not reconstructed by dictionary keys. -/
theorem choose_grounded_trace_with_actual_support405 {s q row ds needs}
    (choice : SupportedChoice404 s q row needs) (safe : ¬ RootCycle s q)
    (support : SupportForest completedChoiceSource404 s needs) (retained : SupportedCenters404 choice)
    (clauses : LiteralVariableWhere403 row)
    (declared : DeclaredOriginalOutputs400 s.core q)
    (typed : ∀ origin : SelectedHeadOrigin395 (row := row) (supportedTape404 choice retained),
      NamedInputAtStoredHead401 s.b6 (supportedFrame404 origin))
    (fixed : ∀ origin : SelectedHeadOrigin395 (row := row) (supportedTape404 choice retained),
      RetainedOutputSources403 (s := s) (supportedFrame404 origin) ∨
        TypedRowsAtOriginalInput403 (s := s) (supportedFrame404 origin))
    (whereDerives : ∀ origin : SelectedHeadOrigin395 (row := row) (supportedTape404 choice retained),
      ∃ trees : List Tree, Nonempty (WhereForest completedChoiceSource404 s
        (frameWhereKids400 (supportedFrame404 origin)) trees) ∧ All₂ Summarizes trees (ds.map Result.selected)) :
    ∃ (e : Event s q) (rule : completedChoiceSource404.elected s q e needs)
        (trees : List Tree) (children : WhereForest completedChoiceSource404 s e.kids trees),
      e.frame.decl = row ∧ Nonempty (GroundedLocalReceipt405 e support) ∧
      Summarizes (.selected e.frame.decl.id trees) (.selected (.node row.id ds)) ∧
      Nonempty (I72.GeneralTree (SourceTrace.selected e safe rule support children) (.node row.id ds)) := by
  obtain ⟨origin⟩ := selected_head_original_origin395 (actual_supported_tape404 choice safe retained)
  obtain ⟨outs,_,_,_⟩ := stored_head_emits_exact_ordered_mixed_values401
    origin unusedPlacement403 (fun _ => emptyCapture403) choice.checked declared s.b6 (typed origin)
  let e : Event s q := ⟨supportedFrame404 origin,origin.pick.head,outs⟩
  have grounded : SupportedEvent404 needs e := ⟨choice,retained,origin,rfl,rfl,clauses⟩
  have exactRows : RetainedVariableOutputs403 e ∨ RetainedTypedValueRows403 e :=
    (fixed origin).elim (fun alias => .inl (addressed_sources_give_real_output_rows403 e alias))
      (fun kinded => .inr (fun i => kinded i (outs i)))
  have rule : completedChoiceSource404.elected s q e needs := .inr ⟨⟨grounded⟩,exactRows⟩
  obtain ⟨trees,⟨whereProof⟩,sorted⟩ := whereDerives origin
  have done : Summarizes (.selected e.frame.decl.id trees) (.selected (.node row.id ds)) :=
    .selected sorted (.selected rfl)
  obtain ⟨tree,_,_⟩ := assemble_at_given_original_trace405
    (SourceTrace.selected e safe rule support whereProof) done
  exact ⟨e,rule,trees,whereProof,rfl,actual_selection_derives_grounded_local_receipt405 safe rule support,
    done,⟨tree⟩⟩

noncomputable def exactC403ProducerInCurrentRules405 {s q t e}
    (original : SourceTrace variableWithNativeK2403 s q t e) :
    SourceTrace completedChoiceSource404 s q t e :=
  preserve_completed_native_sources404
    (preserve_completed_lower_when_admitting_native404 (preserve_c403_derivation404 original))

noncomputable def exactSupportForProducer405 {s q t e d}
    (original : SourceTrace variableWithNativeK2403 s q t (some e))
    (done : Summarizes t (.selected d)) (i : Fin q.demand.outputs.length) :
    SupportForest completedChoiceSource404 s [needOfSelected404 e d i] :=
  .cons (exactC403ProducerInCurrentRules405 original) done rfl .nil

/-- The consumer's chosen source proof was assembled with this very
producer, not merely an arbitrary proof of some equal dictionary.
No client of Classifies can manufacture it from the diagnostic alone.
This instance is structurally unary, with no extra output/where obligation
at the receiving node; its given producer's own tree is arbitrary. -/
theorem original_producer_remains_the_one_consumed405
    {s producer q t e d row a}
    (original : SourceTrace variableWithNativeK2403 s producer t (some e))
    (done : Summarizes t (.selected d)) (i : Fin producer.demand.outputs.length)
    (literal : LiteralInputNeed404 s a (needOfSelected404 e d i))
    (binder : Nat) (inputs : q.demand.arguments = [a]) (head : row.head = [.var binder])
    (scope : GeneralDeclarativeI65.visible s.core q = [row])
    (checked : Checked (authoredRegistry s.core.current))
    (covered : DeclarationCovered s.core.current.environment row)
    (bounds : Bounds s.core.current.ordinary a) (safe : ¬ RootCycle s q)
    (noWhere : row.requirements = []) (noOutputs : q.demand.outputs = []) :
    let need := needOfSelected404 e d i
    let support := exactSupportForProducer405 original done i
    (support.atOriginal 0 (need := need) rfl).source = exactC403ProducerInCurrentRules405 original ∧
    ∃ (caller : Event s q) (rule : completedChoiceSource404.elected s q caller [need])
        (trees : List Tree) (children : WhereForest completedChoiceSource404 s caller.kids trees)
        (lowered : I72.GeneralTree (SourceTrace.selected caller safe rule support children) (.node row.id [])),
      caller.frame.decl = row ∧ Nonempty (GroundedLocalReceipt405 caller support) ∧
      PrioritiesOnTree405 lowered ∧ LedgerMeaning Addresses lowered.ledger ∧
      ∀ m, Fits s m → DictionaryEvidence s m q (.node row.id []) := by
  dsimp only
  let need := needOfSelected404 e d i
  let support := exactSupportForProducer405 original done i
  let choice : SupportedChoice404 s q row [need] :=
    { input := fun b present => by
        rw [inputs] at present
        cases List.mem_singleton.mp present
        exact .viaOutput 0 rfl literal bounds
      checked := checked
      covered := fun r present => by
        rw [scope] at present
        cases List.mem_singleton.mp present
        exact covered
      rowShape := fun r present => by
        rw [scope] at present
        cases List.mem_singleton.mp present
        exact ⟨[binder],head,by simp [inputs]⟩
      sole := scope }
  have ties : SupportedCenters404 choice := by
    have count : choice.row.binders.length = 1 := by simpa [inputs] using choice.row.sameArity
    obtain ⟨n,exactRow⟩ := List.length_eq_one_iff.mp count
    intro eq required
    simp [selectedCenterRows403,selectedInputSpans403,selectedInput403,bindings403,exactRow,inputs] at required
  have absent : ∀ slot : Fin q.demand.outputs.length, False := by
    intro slot
    obtain ⟨i,impossible⟩ := slot
    simp [noOutputs] at impossible
  have clauses : LiteralVariableWhere403 row := by simp [LiteralVariableWhere403,noWhere]
  obtain ⟨caller,rule,trees,children,check,receipt,summary,_⟩ :=
    choose_grounded_trace_with_actual_support405 (ds := []) choice safe support ties clauses
      (fun i => (absent i).elim) (fun _ i => (absent i).elim)
      (fun _ => .inl (fun i => (absent i).elim)) (fun origin => by
        have noKids : frameWhereKids400 (supportedFrame404 origin) = [] := by
          simp [frameWhereKids400,AuthoredBodyFrame393.clauses,supportedFrame404,
            preoutputFrameOfOrigin399,frameAtSource395,noWhere,children]
        exact ⟨[],⟨noKids.symm ▸ .nil⟩,.nil⟩)
  obtain ⟨lowered,_,grounded,_,addresses,_,meaning⟩ :=
    assemble_at_given_original_trace405 (SourceTrace.selected caller safe rule support children) summary
  exact ⟨rfl,caller,rule,trees,children,lowered,check,receipt,grounded,addresses,meaning⟩

end Yulang.GeneralDeclarativeI65.I72
