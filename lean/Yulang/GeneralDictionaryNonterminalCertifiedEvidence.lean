import Yulang.GeneralDictionaryNonterminalNonpointExample
import Yulang.GeneralDictionaryNonpointCertifiedOutput
import Yulang.GeneralDictionaryVariableIntervalLeaf
import Yulang.GeneralDictionaryCollapseReadiness

/-! A checked nonterminal registry, an actual certified improving revision,
and full current source Evidence with the actual emitted nonpoint child.
The certificate uses initial ordinary endpoint equality for every model;
no selected dictionary, output installation, or Stable result is claimed. -/
set_option linter.unusedSimpArgs false
namespace Yulang.GeneralDictionaryNonterminalCertifiedEvidence
open GeneralDictionaryNonterminalNonpointExample (declaration child outputRoot body checked names variable_clauses)
open GeneralDictionaryNonpointStrict (model)
open GeneralDictionaryNonpointCertifiedOutput (source context revision bounds shape revised_models)
open GeneralDeclarations GeneralDeclarationPatterns GeneralNominalRecursiveCandidates
open GeneralNominalRecursiveInspection GeneralDictionaryRecursiveEvidence
abbrev leaf : Declaration := ⟨32,0,[.var 8],[],[],[]⟩

theorem queries : GeneralNominalInspection.queries source GeneralDictionaryNonpointStrict.interpretation declaration = [GeneralDictionarySemanticCollapse.query shape] :=
  GeneralDictionaryNonpointCertifiedOutput.queries
abbrev registry : Registry := ⟨source.constructors,GeneralDictionaryNonpointStrict.roles,[declaration,leaf]⟩
noncomputable abbrev current := GeneralDictionarySemanticCollapseBranch.currentContext revision

noncomputable abbrev captures := bindings current.state (report current declaration bounds)
noncomputable abbrev frame := GeneralNominalAllocation.frame (roles := GeneralDictionaryNonpointStrict.roles)
  current.state registry outputRoot.identity captures
noncomputable abbrev occurrence := GeneralDictionaryEmissionPlans.occurrence frame
  (GeneralDeclarationDemands.emit outputRoot.identity declaration child
    (checked.signature.2.2.2 child (List.mem_singleton_self _))
    (frame.capture declaration.id) (frame.allocation declaration.id child))

theorem children_exact : GeneralNominalAllocation.children current.state registry outputRoot declaration checked captures = [occurrence] := by
  have canonical : GeneralCanonicalChildOrder.canonicalDeclaration declaration = declaration := by decide +kernel
  simp only [GeneralNominalAllocation.children,GeneralDictionaryEmissionPlans.children,
    GeneralCanonicalChildOrder.canonicalEmit,canonical]
  rfl

theorem captures_exact : captures = [(7,3,4)] := by
  change bindings (GeneralDictionarySemanticCollapseBranch.currentContext revision).state (report (GeneralDictionarySemanticCollapseBranch.currentContext revision) declaration [(shape.root,shape.root)]) = _
  rw [(GeneralDictionarySemanticCollapseBranch.reports shape declaration queries).2]
  rfl

theorem child_arguments : arguments current occurrence = some [((3 : Fin 5),(4 : Fin 5))] := by
  simp [arguments,GeneralNominalCandidates.arguments,occurrence,
    GeneralDictionaryEmissionPlans.occurrence,GeneralDeclarationDemands.emit,
    GeneralDeclarationDemands.childDemand,GeneralDeclarationDemands.inputInterval,
    frame,GeneralNominalAllocation.frame,GeneralNominalAllocation.capture,captures_exact,
    GeneralNominalAllocation.occurrences,normalize,List.ofFn_succ]
  rfl

theorem leaf_checked : DeclarationChecked registry.constructors GeneralDictionaryNonpointStrict.roles leaf := by
  constructor
  · simp [Declaration.Signature,leaf,GeneralDictionaryNonpointStrict.roles,GeneralDeclarationExamples.roles,GeneralDeclarationExamples.bareRole]
  · simp [Declaration.Identified,Declaration.outputNames,leaf]
  · simp [Declaration.Produced,leaf]
  · simp [Declaration.OutputOnly,Declaration.outputNames,leaf]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,leaf,normalizeArgs,normalize,variablesArgs,Pattern.variables]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,leaf]
  · simp [leaf]
  · simp [leaf]
  · simp [leaf]
  · simp [leaf]

theorem metadata : Metadata registry current := by
  refine ⟨rfl,?_⟩
  intro name primitive found
  cases found

theorem leaf_query : GeneralNominalInspection.queries current.state current.interpretation leaf = [.variables [8]] := by
  simp [GeneralNominalInspection.queries,Declaration.normalHead,leaf,normalizeArgs,normalize,GeneralNominalInspection.translate]

theorem child_instance : Instance registry current model occurrence leaf.id [] := by
  apply GeneralDictionaryVariableIntervalLeaf.instance_of_interval current registry occurrence leaf
    (by simp [registry]) leaf_checked 8 ((3 : Fin 5),(4 : Fin 5)) leaf_query rfl rfl rfl rfl child_arguments metadata model revised_models
  change CommonNominalFullCarrier.Subtype (model 3).1 (model 4).1
  rw [GeneralDictionaryNonpointStrict.at_lower,GeneralDictionaryNonpointStrict.at_upper]
  exact GeneralDictionaryNonpointStrict.bottom_leaf

theorem child_evidence : Evidence registry current model occurrence (.node leaf.id []) :=
  (evidence_leaf_iff registry current model occurrence leaf.id).mpr child_instance

theorem parent_branch : BranchModels registry current outputRoot declaration checked bounds model := by
  refine ⟨?_,?_,?_⟩
  · exact GeneralDictionaryNonpointCertifiedOutput.current_branch.1
  · exact GeneralDictionaryNonpointCertifiedOutput.current_branch.2.1
  · unfold generated
    rw [GeneralDictionaryVariableWhereRequests.bare_requests _ _ _ _ _ _ variable_clauses]
    have old := GeneralDictionaryNonpointCertifiedOutput.current_branch.2.2
    unfold generated at old
    rw [GeneralNominalFiniteAssociatedFacts.terminal_requests _ _ _ _ _ _ rfl] at old
    exact old

theorem parent_ready : RequestReady registry current outputRoot declaration checked bounds := by
  constructor
  · intro output member
    cases List.mem_singleton.mp member
    exact ⟨⟨43,0,.var 7⟩,by simp [declaration],rfl⟩
  · unfold generated
    rw [GeneralDictionaryVariableWhereRequests.bare_requests _ _ _ _ _ _ variable_clauses]
    simp [GeneralNominalMaterialization.generated,GeneralNominalMaterialization.rootRequests,declaration,outputRoot,GeneralNominalInspection.translate,normalize,GeneralNominalMaterialization.schema,GeneralNominalMaterialization.Schema.append]

theorem parent_instance : Instance registry current model outputRoot declaration.id [occurrence] := by
  refine ⟨declaration,by simp [registry],checked,rfl,rfl,bounds,?_,?_,parent_ready,children_exact.symm,metadata,parent_branch⟩
  · change arguments context outputRoot = some bounds
    decide +kernel
  · exact (GeneralDictionaryCollapseReadiness.finished shape declaration queries).2

theorem full_evidence : Evidence registry current model outputRoot (.node declaration.id [.node leaf.id []]) :=
  evidence_node registry current model outputRoot declaration.id [occurrence] [.node leaf.id []]
    parent_instance (.cons child_evidence .nil)

theorem positive_nonterminal_evidence :
    declaration.requirements.length = 1 ∧ body.variables.length = 1 ∧
    GeneralNominalAllocation.children current.state registry outputRoot declaration checked captures = [occurrence] ∧
    arguments current occurrence = some [((3 : Fin 5),(4 : Fin 5))] ∧
    (model 3).1 ≠ (model 4).1 ∧
    Evidence registry current model outputRoot (.node declaration.id [.node leaf.id []]) :=
  ⟨rfl,rfl,children_exact,child_arguments,GeneralDictionaryNonpointStrict.nonpoint_leaf.2,full_evidence⟩
open GeneralNominalReobservationSteps GeneralNominalSaturationState
abbrev tracked := GeneralNominalSupport.initial context outputRoot
noncomputable abbrev after := GeneralDictionaryNonpointCertifiedOutput.after

theorem registry_checked : Checked registry := by
  constructor
  · simp [registry,declaration,leaf]
  · intro d member
    simp only [registry,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact checked
    · exact leaf_checked

theorem initial_source : GeneralNominalSourceFormation.InitialSource registry context outputRoot := by
  have old := GeneralDictionaryNonpointCertifiedOutput.initial_source
  exact ⟨old.roles_agree,old.metadata,old.linked,old.intervals,old.below_seed,old.unallocated⟩

theorem certified : Certified revision := GeneralDictionaryNonpointCertifiedOutput.certified

theorem improves : Improves revision := GeneralDictionaryNonpointCertifiedOutput.improves

theorem actual_value_step : GeneralNominalValueSteps.Step registry outputRoot tracked after :=
  ⟨outputRoot,.root,.administrative outputRoot revision.result (.reobserve outputRoot revision certified improves)⟩

theorem formed : GeneralNominalValueSteps.SourceFormed registry outputRoot after :=
  .update (.initial context initial_source) actual_value_step

theorem reachable : B4TargetV5.Reachable
    (GeneralNominalValueBoundary.boundary GeneralDictionaryNonpointStrict.roles) registry outputRoot after :=
  ⟨tracked,⟨context,initial_source,rfl⟩,.tail .refl actual_value_step⟩

theorem result_models : GeneralNominalSaturationState.Models after.current model :=
  GeneralDictionaryNonpointCertifiedOutput.result_models

/-- Same registry, root, reached context and model throughout. The Evidence
contains the actual canonical child, whose input endpoints differ semantically. -/
theorem reachable_nonterminal_evidence :
    Checked registry ∧
    GeneralNominalValueSteps.Step registry outputRoot tracked after ∧
    B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary GeneralDictionaryNonpointStrict.roles) registry outputRoot after ∧
    GeneralNominalValueSteps.SourceFormed registry outputRoot after ∧
    GeneralNominalSaturationState.Models after.current model ∧
    declaration.requirements.length = 1 ∧ body.variables.length = 1 ∧
    (model 3).1 ≠ (model 4).1 ∧
    Evidence registry after.current.context model outputRoot (.node declaration.id [.node leaf.id []]) :=
  ⟨registry_checked,actual_value_step,reachable,formed,result_models,rfl,rfl,
    GeneralDictionaryNonpointStrict.nonpoint_leaf.2,full_evidence⟩
end Yulang.GeneralDictionaryNonterminalCertifiedEvidence
