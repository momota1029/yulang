import Yulang.GeneralDeclarativeI65I72GroundedAssembly405

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72
open GeneralDeclarativeI65
open CommonRoleOutermostResolver (Dictionary Summarizes Tree)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarativeWitnessModeCoverage357 (DeclarationCovered)
open GeneralDeclarations (Checked)

theorem supported_classifies_embeds_exactly_in_completed_choice405 {s q result}
    (chosen : Classifies supportedVariableSource404 s q result) :
    Classifies completedChoiceSource404 s q result := by
  obtain ⟨t,event,⟨actual⟩,summary⟩ := chosen
  exact ⟨t,event,⟨preserve_completed_native_sources404
    (preserve_completed_lower_when_admitting_native404 actual)⟩,summary⟩

/-- Nonvacuous instantiation of the repaired priority/ledger path.
The consumer classification is *derived*, not an assumption. The
producer is a real, independently completed source derivation in the
same State; exact predicates concern literal written unary input and
the current retained equation, not fitted equality used for election.
This is a quantified theorem over existing source rules, not a fixture. -/
theorem actual_producer_runs_grounded_consumer_replay405
    {s producer q t e dict row a}
    (source : SourceTrace variableWithNativeK2403 s producer t (some e))
    (done : Summarizes t (.selected dict)) (i : Fin producer.demand.outputs.length)
    (literal : LiteralInputNeed404 s a (needOfSelected404 e dict i))
    (binder : Nat) (inputs : q.demand.arguments = [a]) (head : row.head = [.var binder])
    (scope : GeneralDeclarativeI65.visible s.core q = [row])
    (checked : Checked (authoredRegistry s.core.current))
    (covered : DeclarationCovered s.core.current.environment row)
    (bounds : Bounds s.core.current.ordinary a) (safe : ¬RootCycle s q)
    (noWhere : row.requirements = []) (noOutputs : q.demand.outputs = []) :
    let d := Dictionary.node row.id []
    ((⟨a.lower,.nominal literal.key literal.arguments⟩ : Equation) ∈ s.core.current.ordinary.equations) ∧
      ∃ (t : Tree) (ev : Option (Event s q)) (trace : SourceTrace completedChoiceSource404 s q t ev)
          (tree : I72.GeneralTree trace d) (ledger : Ledger s q d),
        Summarizes t (.selected d) ∧ PrioritiesOnTree405 tree ∧
        CanonicalReplay tree ledger ∧ LedgerMeaning Addresses ledger ∧
        ∀ m, Fits s m → LedgerMeaning (LocalMeaning m) ledger ∧ DictionaryEvidence s m q d := by
  obtain ⟨selected,lower⟩ := actual_completed_B6_producer_opens_unary_consumer404
    source done i literal binder inputs head scope checked covered bounds safe noWhere noOutputs
  refine ⟨lower,?_⟩
  obtain ⟨t,ev,trace,tree,ledger,summary,priority,canonical,addresses,meaning⟩ :=
    completed_choice_same_priority_and_ledger405 (supported_classifies_embeds_exactly_in_completed_choice405 selected)
  exact ⟨t,ev,trace,tree,ledger,summary,priority,canonical,addresses,fun m fit =>
    ⟨(meaning m fit).1,(meaning m fit).2.2⟩⟩

end Yulang.GeneralDeclarativeI65.I72
