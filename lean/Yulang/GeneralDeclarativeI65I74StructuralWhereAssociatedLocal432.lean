import Yulang.GeneralDeclarativeI65I74StructuralWhereDeclaredOutput432

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.WhereAssociated432
open GeneralDeclarativeI65 StructuralWhere427 StructuralWhere428
open GeneralDeclarations (OutputBinder Equation Checked)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarativeWitnessConstructorModes357 (Use)
open GeneralDeclarativeWitnessSparseIntervals357 (names)
open GeneralDeclarativeWhere319 (Capture)
open CommonDeclaredNominalInspection (Parameter)
open CommonRecursiveNominalIntervals (effectiveParameter)

/-- Scoped independent local source for the literal positive Wrap
shape. The raw root gate, authored registry and exact input captures
are independent of the report and children. Related typed output
must come from the original atlas/body and be retained at the fixed
target. No proof that the child or parent selected is a premise.
This is a declarative kernel, not an installed executable branch. -/
structure OriginalAssociatedWrap432 {s : I72.State} {q : Request}
    (e : Event s q) where
  checked : Checked (authoredRegistry s.core.current)
  onlyVisible : visible s.core q = [e.frame.decl]
  rawRoot : ¬ RootCycle s q
  headBinder : Nat
  ctor : Nat
  arg : Capture
  input : q.demand.arguments = [arg]
  literalHead : e.frame.decl.head = [.app ctor [.var headBinder]]
  actualNames : positiveCaptureOf427 e.head = some e.frame.input
  outputBinder : OutputBinder
  binderInSource : outputBinder ∈ e.frame.decl.outputBinders
  literalRhs : Equation
  origin : OriginalWhereBinder395 e.frame outputBinder literalRhs
  originalWhere : e.frame.decl.requirements = [origin.entry.clause]
  independentInput : origin.entry.clause.arguments = [.var headBinder]
  onlyParentOutput : q.demand.outputs.length = 1
  indexedParentOutput : Fin q.demand.outputs.length
  body : (e.outputs indexedParentOutput).body = .explicit literalRhs
  normalized : GeneralDeclarationPatterns.normalize
      (GeneralDeclarativeOutputs320.bodyPattern (e.outputs indexedParentOutput).body) =
    .app ctor [.var outputBinder.name]
  parameter : Parameter
  use : Use s.core.current.environment ctor 1
  authoredModes : names use.mode 1 = some [parameter]
  matchingModeTable : s.core.modes[ctor]? = some [parameter]
  valueKind : parameter.kind = .value
  invariant : (effectiveParameter false parameter).variance = .invariant
  actualTypedRhs : HEq (e.outputs indexedParentOutput).plan
    (invariantUnaryValuePlan432 ctor outputBinder.name parameter use authoredModes
      matchingModeTable valueKind invariant)
  retained : RetainedTypedValueRows403 e

def associatedWrapLocal432 : SourcePrimitives where
  elected _ _ e needs := needs = [] ∧ Nonempty (OriginalAssociatedWrap432 e)
  other _ _ _ _ := False

theorem original_associated_wrap_local_law432 : SelectedLaw428 associatedWrapLocal432 := by
  intro s q e needs picked m fit
  obtain ⟨source⟩ := picked.2
  exact ⟨⟨source_head_sound e.head m fit,
    fun i => original_named_mixed_output_meaning401 m (e.outputs i) source.checked⟩,
    retained_typed_rows_satisfy_fixed_targets403 source.retained m fit⟩

def associatedWhereKernel432 : SourcePrimitives .withEndpoint where
  elected := (ruleUnion428 StructuralWhere431.R15.named426 associatedWrapLocal432).elected
  other := (ruleUnion428 StructuralWhere431.R15.named426 associatedWrapLocal432).other

theorem associated_named_law432 : SelectedLaw428 associatedWhereKernel432.named426 :=
  union_local_law428 StructuralWhere431.named_law431 original_associated_wrap_local_law432

theorem dictionary_sound_for_associated_where_kernel432 : DictionarySound associatedWhereKernel432 := by
  intro s q d source m fit
  rcases classification_has_exact_lane_rule426 source with named|endpoint
  · obtain ⟨_,_,⟨actual⟩,summary⟩ := named
    exact actual_named_trace_same_model_dictionary428 associated_named_law432 actual m fit d summary
  · obtain ⟨e,⟨kept⟩,same⟩ := endpoint
    cases same
    exact original_projected_leaf_with_retention_has_dictionary_evidence426 e kept m fit

end Yulang.GeneralDeclarativeI65.I72.WhereAssociated432
