import Yulang.GeneralDeclarativeI65I72SupportedClassifies404

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72
open GeneralDeclarativeI65
open CommonRoleOutermostResolver (All₂ Dictionary Result Summarizes)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarations (Declaration Checked)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarativeWitnessModeCoverage357 (DeclarationCovered)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeHead320 (Equation environment)
open GeneralNominalCenteredHeadMatExpressions (Expr value)
open CommonNominalFullCarrier (Equivalent)

/-- Mint the only possible expected receipt from the actual producer's
same selected event, at its literal original output index. -/
def needOfSelected404 {s q} (event : Event s q) (dict : Dictionary)
    (i : Fin q.demand.outputs.length) : OutputNeed s :=
  ⟨q,dict,i,(event.outputs i).receipt⟩

noncomputable def one_actual_c403_producer404 {s q t e dict}
    (trace : SourceTrace variableWithNativeK2403 s q t (some e))
    (done : Summarizes t (.selected dict)) (i : Fin q.demand.outputs.length) :
    SupportForest supportedVariableSource404 s [needOfSelected404 e dict i] :=
  .cons (preserve_c403_derivation404 trace) done rfl .nil

theorem producer_receipt_owns_exact_consumer_lower404 {s q t e dict}
    (trace : SourceTrace variableWithNativeK2403 s q t (some e))
    (done : Summarizes t (.selected dict)) (i : Fin q.demand.outputs.length) {a : Capture}
    (literal : LiteralInputNeed404 s a (needOfSelected404 e dict i)) :
    (⟨a.lower,.nominal literal.key literal.arguments⟩ : Equation) ∈
      s.core.current.ordinary.equations :=
  support_at_literal_ordinal_yields_nominal404 supported_rules_keep_exact_rows404
    (one_actual_c403_producer404 trace done i) 0 rfl literal

theorem completed_B6_head_means_same_consumer_lower404 {s q t e dict}
    (trace : SourceTrace variableWithNativeK2403 s q t (some e))
    (done : Summarizes t (.selected dict)) (i : Fin q.demand.outputs.length) {a : Capture}
    (literal : LiteralInputNeed404 s a (needOfSelected404 e dict i)) (m : Model) (fit : Fits s m) :
    Equivalent (m.assignment a.lower).1
      (value (environment m.assignment) .actual (.nominal literal.key literal.arguments)) :=
  fit.1.1.2 _ (producer_receipt_owns_exact_consumer_lower404 trace done i literal)

private def unaryChoiceFromProducer404 {s q d need a} (binder : Nat)
    (input : q.demand.arguments = [a]) (writes : d.head = [.var binder])
    (visible : GeneralDeclarativeI65.visible s.core q = [d])
    (checked : Checked (authoredRegistry s.core.current))
    (covered : DeclarationCovered s.core.current.environment d)
    (literal : LiteralInputNeed404 s a need) (range : Bounds s.core.current.ordinary a) :
    SupportedChoice404 s q d [need] where
  input := fun b present => by
    rw [input] at present
    cases List.mem_singleton.mp present
    exact .viaOutput 0 rfl literal range
  checked := checked
  covered := fun row present => by
    rw [visible] at present
    cases List.mem_singleton.mp present
    exact covered
  rowShape := fun row present => by
    rw [visible] at present
    cases List.mem_singleton.mp present
    exact ⟨[binder],writes,by rw [input]; rfl⟩
  sole := visible

private theorem no_ties_in_original_unary404 {s q d needs a}
    (choice : SupportedChoice404 s q d needs) (input : q.demand.arguments = [a]) :
    SupportedCenters404 choice := by
  have h : choice.row.binders.length = 1 := by simpa [input] using choice.row.sameArity
  obtain ⟨binder,list⟩ := List.length_eq_one_iff.mp h
  intro eq selected
  simp [selectedCenterRows403,selectedInputSpans403,selectedInput403,bindings403,list,input] at selected

/-- Entire narrow producer-to-consumer classification, not a
classification supplied as a premise for the consumer. Arbitrary
actual selected C403 producer trees are allowed. The consumer's one
exact source-known argument, visible singleton and authored head are
read before producing the dictionary; no additional consumer output
equation or center tie is assumed (there are none in this fragment). -/
theorem actual_completed_B6_producer_opens_unary_consumer404
    {s producer q t e dict d a}
    (trace : SourceTrace variableWithNativeK2403 s producer t (some e))
    (done : Summarizes t (.selected dict)) (i : Fin producer.demand.outputs.length)
    (literal : LiteralInputNeed404 s a (needOfSelected404 e dict i))
    (binder : Nat) (input : q.demand.arguments = [a]) (written : d.head = [.var binder])
    (visible : GeneralDeclarativeI65.visible s.core q = [d])
    (checked : Checked (authoredRegistry s.core.current))
    (covered : DeclarationCovered s.core.current.environment d)
    (bounds : Bounds s.core.current.ordinary a) (safe : ¬RootCycle s q)
    (noWhere : d.requirements = []) (noOutputs : q.demand.outputs = []) :
    Classifies supportedVariableSource404 s q (.selected (.node d.id [])) ∧
      ((⟨a.lower,.nominal literal.key literal.arguments⟩ : Equation) ∈ s.core.current.ordinary.equations) := by
  let choice := unaryChoiceFromProducer404 binder input written visible checked covered literal bounds
  have absent : ∀ slot : Fin q.demand.outputs.length, False := by
    intro slot
    obtain ⟨n,impossible⟩ := slot
    simp [noOutputs] at impossible
  refine ⟨?_,producer_receipt_owns_exact_consumer_lower404 trace done i literal⟩
  apply select_with_completed_inputs404 choice safe (one_actual_c403_producer404 trace done i)
    (no_ties_in_original_unary404 choice input)
  · intro clause present
    rw [noWhere] at present
    cases present
  · intro slot; exact (absent slot).elim
  · intro origin slot; exact (absent slot).elim
  · intro origin
    exact .inl (fun slot => (absent slot).elim)
  · intro origin
    have kids : frameWhereKids400 (supportedFrame404 origin) = [] := by
      simp [frameWhereKids400,AuthoredBodyFrame393.clauses,supportedFrame404,
        preoutputFrameOfOrigin399,frameAtSource395,noWhere,children]
    rw [kids]
    exact .nil

/-- An incomplete producer contributes no head support, but its exact
self-ring at the *consumer input* remains in the raw ordinary graph.
K2 rejects before any attempt to build that unavailable dependency. -/
theorem unfinished_output_still_rejects_raw_root404
    {s q a need} (seen : a ∈ q.demand.arguments)
    (incomplete : ¬ Classifies supportedVariableSource404 s need.producer (.selected need.dictionary))
    {doneTag : Nat → Prop} (origins : GeneralDeclarativeOrigins321.Supported s.core.current.ordinary doneTag)
    (tag owner : Nat)
    (retained : origins.derivesFrom (⟨a.lower,.nominal tag [.variable a.lower]⟩ : Equation) (.output owner))
    (unready : ∀ kind, origins.derivesFrom (⟨a.lower,.nominal tag [.variable a.lower]⟩ : Equation) kind →
        ∃ i, kind = .output i ∧ ¬ doneTag i) :
    (⟨a.lower,.nominal tag [.variable a.lower]⟩ : Equation) ∉
        (GeneralDeclarativeOrigins321.restriction origins).equations ∧
      ¬ Nonempty (ExactOutputSupport supportedVariableSource404 s need) ∧
      Classifies supportedVariableSource404 s q .rejected := by
  refine ⟨GeneralDeclarativeOrigins321.pending_only origins _ unready,
    no_finite_selected_producer_no_support404 incomplete,?_⟩
  exact (raw_k2_before_completed_inputs404 ⟨a,seen,GeneralDeclarativeK2Alias321.cycle_in_alias_graph
    (GeneralDeclarativeGraphRows321.pending_nominal_self_cycle origins owner retained)⟩).1

end Yulang.GeneralDeclarativeI65.I72
