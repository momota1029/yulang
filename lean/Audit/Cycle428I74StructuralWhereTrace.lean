import Yulang.GeneralDeclarativeI65I74StructuralWhereFold428
import Yulang.GeneralDeclarativeI65I74StructuralWhereForestAuditSupport430

set_option maxRecDepth 3200
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.StructuralWhereTrace428
open GeneralDeclarativeI65 StructuralWhere427 StructuralWhere428
open StructuralWhereForestFixture430
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarations (DeclarationChecked)
open CommonRoleOutermostResolver (Dictionary Summarizes Tree)

theorem original_parent_header428 : DeclarationChecked
    (authoredRegistry p.state.core.current).constructors
    (authoredRegistry p.state.core.current).roles twoFrame.decl := by
  let e := p.state.core.current.environment
  have roles : GeneralSourceMetadataRoles291.Valid e.source.roles :=
    (GeneralSourceMetadataRoles291.check_exact _).mp (by decide +kernel)
  have cov := (GeneralDeclarativeWitnessModeCoverage357.check_exact roles).mp (by decide +kernel)
  have authored : parentTwo ∈ e.source.declarations := by decide +kernel
  apply every_original_closed_where_clause_passes_parent_header427 (cov.1 _ authored)
    (by decide +kernel) rfl
  intro c used
  change c ∈ [firstClause,secondClause] at used
  simp only [List.mem_cons,List.not_mem_nil,or_false] at used
  rcases used with rfl|rfl <;> exact ⟨rfl,by decide +kernel⟩

/-- Isolated audit relation. The constructor sees the selected
original local source and raw candidate facts; it does not see the
where forest, a classifier answer, a model, or an offered dictionary.
This is not a canonical/R15 installation. -/
private inductive TestScoped (s : I72.State) : (q : Request) → Event s q → Type where
  | parent {q} {f : AuthoredBodyFrame393 s.core q}
      (r : OriginalPreparedRoot427 f)
      (header : DeclarationChecked (authoredRegistry s.core.current).constructors
        (authoredRegistry s.core.current).roles f.decl)
      (whereExists : f.decl.requirements ≠ []) (noOutput : q.demand.outputs = []) :
    TestScoped s q (parentEvent428 r noOutput)
  | child {q} {f : AuthoredBodyFrame393 s.core q} {i}
      (row : ReviewedWhereAt427 f i) :
    TestScoped s row.original.child (leafEvent428 row)

private def probeRules : SourcePrimitives where
  elected s q e needs := needs = [] ∧ Nonempty (TestScoped s q e)
  other _ _ _ _ := False

private theorem actualLeafLocal : WhereLocal428 probeRules p.state p.root twoFrame :=
  fun _ row => ⟨rfl,⟨.child row⟩⟩
private theorem actualRootLocal :
    probeRules.elected p.state p.root (parentEvent428 prepared rfl) [] :=
  ⟨rfl,⟨.parent prepared original_parent_header428 (by decide +kernel) rfl⟩⟩

private def actualTrace :=
  parentTrace428 prepared rfl actualRootLocal actualLeafLocal recovered

private theorem replayedDict : recovered.dictionaries = [.node 219 [],.node 219 []] :=
  actual_authored_order_keeps_two_equal_denoting_where_arguments_distinct427.2.2.1

/-- Uses the real named Classifies entry with a deliberately isolated
local primitive whose underlying evidence is independent of result and
model. It does not call or claim a modification of the public checker. -/
theorem original_two_where_goes_through_the_named_classifier428 :
    Classifies probeRules p.state p.root (.selected (.node 218 [.node 219 [],.node 219 []])) := by
  refine ⟨_,_,⟨actualTrace⟩,?_⟩
  have exactResult := actual_named_tree_has_exact_source_ordered_dictionary428 recovered
  rw [replayedDict] at exactResult
  exact exactResult

theorem actual_selected_where_trace_preserves_literal_ordinals_and_events428
    (i : Fin twoFrame.decl.requirements.length) :
    ∃ a : ReviewedWhereAt427 twoFrame i.val,
      TraceChild428 actualTrace i.val a.original.child (leafEvent428 a) ∧
      (parentEvent428 prepared rfl).kids[i.val]? = some a.original.child ∧
      a.original.child.occurrence = [71] ++ [i.val] ∧
      (leafEvent428 a).frame.decl = a.actual.positive.decl ∧
      twoFrame.names.input a.original.binder = prepared.visiblePoint.positive.capture a.original.binder ∧
      p.state.core.current.ordinary.equations[a.original.rowOrdinal]? =
        some (writtenRow427 twoFrame a.original.name a.original.label a.original.binder) :=
  original_where_position_is_actual_selected_trace_child428 prepared original_parent_header428
    rfl actualRootLocal actualLeafLocal recovered i

private theorem original_rule_local_meaning428 : SelectedLaw428 probeRules := by
  intro s q e needs admitted m fit
  obtain ⟨admission⟩ := admitted.2
  cases admission with
  | parent root _ _ empty =>
    exact no_output_ordinary_event_same_model_semantics428 _ 
      (root.declaration ▸ root.visiblePoint.positive.head) empty m fit
  | child row =>
    exact no_output_ordinary_event_same_model_semantics428 (leafFrame428 row)
      row.actual.positive.head row.noOutputs m fit

theorem all_fitting_models_of_actual_original_where_trace_have_its_dictionary428
    (m : I72.Model) (fit : I72.Fits p.state m) :
    DictionaryEvidence p.state m p.root (.node 218 [.node 219 [],.node 219 []]) :=
  dictionary_sound_from_actual_named_local_law428 original_rule_local_meaning428 _ _ _
    original_two_where_goes_through_the_named_classifier428 m fit

theorem the_named_where_example_is_not_vacuous428 :
    I72.Fits p.state fitModel ∧
      DictionaryEvidence p.state fitModel p.root (.node 218 [.node 219 [],.node 219 []]) :=
  ⟨two_source_model_fits427,
    all_fitting_models_of_actual_original_where_trace_have_its_dictionary428
      fitModel two_source_model_fits427⟩

#print axioms actual_named_trace_same_model_dictionary428
#print axioms dictionary_sound_for_actual_mixed_named_rule_traces428
#print axioms all_fitting_models_of_actual_original_where_trace_have_its_dictionary428
#print axioms the_named_where_example_is_not_vacuous428
#print axioms named_selected_leaf_uses_literal_ordinal_and_actual_event428
#print axioms original_where_position_is_actual_selected_trace_child428
#print axioms actual_named_tree_has_exact_source_ordered_dictionary428
#print axioms original_parent_header428
#print axioms original_two_where_goes_through_the_named_classifier428
#print axioms actual_selected_where_trace_preserves_literal_ordinals_and_events428

end Yulang.GeneralDeclarativeI65.I72.StructuralWhereTrace428
