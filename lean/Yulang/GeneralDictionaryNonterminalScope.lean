import Yulang.GeneralDictionaryNonterminalNonpointBranch
import Yulang.GeneralNominalWhereAssociatedFacts
import Yulang.GeneralDictionaryHeadlessRealization

/-! Checked variable-name scope for actual nonterminal parent replay. A separate
syntactic normal-form or variable-normalization condition handles named where
RHSs without assuming generated schema scope or current model truth. -/
namespace Yulang.GeneralDictionaryNonterminalScope
open GeneralDeclarations GeneralDeclarationPatterns GeneralNominalMaterialization
open GeneralNominalRecursiveCandidates
open GeneralDictionaryVariableWhereRequests

def NormalizedOutputScope (declaration : Declaration) : Prop :=
  ∀ clause ∈ declaration.requirements, ∀ equation ∈ clause.outputs,
    ∀ name ∈ (normalize equation.rhs).variables,
      name ∈ declaration.inputNames ∨ name ∈ declaration.outputNames

theorem normalized_outputs (declaration : Declaration) (scope : declaration.Scoped)
    (normal : ∀ clause ∈ declaration.requirements, ∀ equation ∈ clause.outputs,
      normalize equation.rhs = equation.rhs) : NormalizedOutputScope declaration := by
  intro clause hc equation he name hn
  rw [normal clause hc equation he] at hn
  exact scope.2.2 clause hc equation he name hn

theorem variable_outputs (declaration : Declaration) (scope : declaration.Scoped)
    (variables : ∀ clause ∈ declaration.requirements, ∀ equation ∈ clause.outputs,
      ∃ name, normalize equation.rhs = .var name) : NormalizedOutputScope declaration := by
  intro clause hc equation he name hn
  obtain ⟨binder,eq⟩ := variables clause hc equation he
  rw [eq] at hn
  have same : name = binder := List.mem_singleton.mp hn
  subst name
  exact scope.2.2 clause hc equation he binder
    (GeneralDictionaryHeadlessRealization.normalized_var_occurs _ _ eq)

theorem request_scope (state : GeneralNominalState.State) (registry : Registry)
    (root : GeneralSourceDictionaries.Occurrence roles) (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (captures : GeneralNominalAllocation.Bindings) (variables : VariableInputs declaration)
    (outputs : NormalizedOutputScope declaration) :
    ∀ request ∈ requests state registry root declaration checked captures,
      ∀ name ∈ (normalize request.pattern).variables,
        name ∈ declaration.inputNames ∨ name ∈ declaration.outputNames := by
  intro request member name hn
  rcases GeneralNominalWhereAssociatedFacts.request_witness state registry root declaration checked captures
    variables request member with rootRequest | emitted
  · obtain ⟨output,_,equation,found,rfl⟩ := rootRequest
    exact checked.scope.2.1 equation (List.mem_of_find?_eq_some found) name hn
  · obtain ⟨clause,hc,equation,he,rfl⟩ := emitted
    exact outputs clause hc equation he name hn

theorem generated_scope (context : Context) (registry : Registry)
    (root : GeneralSourceDictionaries.Occurrence roles) (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (bounds : List (GeneralNominalInspection.Bounds context.state))
    (variables : VariableInputs declaration) (outputs : NormalizedOutputScope declaration) :
    ∀ entry ∈ (GeneralNominalRecursiveCandidates.generated registry context root declaration checked bounds).variables,
      entry.name ∈ declaration.inputNames ∨ entry.name ∈ declaration.outputNames := by
  exact GeneralDictionaryActualSchemaScope.generated_scoped _ _ _ _
    (request_scope _ _ _ _ _ _ variables outputs)

open GeneralDictionarySemanticCollapse GeneralDictionarySemanticCollapseBranch
variable {roles : Roles.RoleDecls} {state : GeneralNominalSaturationState.State roles}
variable {revision : GeneralNominalReobservationSteps.Revision state}

/-- Nonterminal parent replay with schema scope discharged from declaration
scope and normalized output syntax. It does not assert child Evidence. -/
theorem branch (s : Shape revision) (registry : Registry)
    (root : GeneralSourceDictionaries.Occurrence roles) (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (queries : GeneralNominalInspection.queries state.context.state state.context.interpretation declaration = [query s])
    (names : declaration.inputNames = [s.binder]) (variables : VariableInputs declaration)
    (outputs : NormalizedOutputScope declaration)
    (model : GeneralNominalCommonBridge.Assignment)
    (old : BranchModels registry state.context root declaration checked [(s.root,s.root)] model)
    (current : GeneralNominalState.Models revision.snapshot model) :
    BranchModels registry (currentContext revision) root declaration checked [(s.root,s.root)] model := by
  apply GeneralDictionaryNonterminalNonpointBranch.branch s registry root declaration checked queries names
    variables _ model old current
  intro entry member notOutput
  have inside := (generated_scope _ _ _ _ _ _ variables outputs entry member).resolve_right notOutput
  simpa [names] using inside

theorem normal_form_branch (s : Shape revision) (registry : Registry)
    (root : GeneralSourceDictionaries.Occurrence roles) (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (queries : GeneralNominalInspection.queries state.context.state state.context.interpretation declaration = [query s])
    (names : declaration.inputNames = [s.binder]) (variables : VariableInputs declaration)
    (normal : ∀ clause ∈ declaration.requirements, ∀ equation ∈ clause.outputs,
      normalize equation.rhs = equation.rhs)
    (model : GeneralNominalCommonBridge.Assignment)
    (old : BranchModels registry state.context root declaration checked [(s.root,s.root)] model)
    (current : GeneralNominalState.Models revision.snapshot model) :
    BranchModels registry (currentContext revision) root declaration checked [(s.root,s.root)] model :=
  branch s registry root declaration checked queries names variables
    (normalized_outputs declaration checked.scope normal) model old current

theorem variable_output_branch (s : Shape revision) (registry : Registry)
    (root : GeneralSourceDictionaries.Occurrence roles) (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (queries : GeneralNominalInspection.queries state.context.state state.context.interpretation declaration = [query s])
    (names : declaration.inputNames = [s.binder]) (variables : VariableInputs declaration)
    (outputs : ∀ clause ∈ declaration.requirements, ∀ equation ∈ clause.outputs,
      ∃ name, normalize equation.rhs = .var name)
    (model : GeneralNominalCommonBridge.Assignment)
    (old : BranchModels registry state.context root declaration checked [(s.root,s.root)] model)
    (current : GeneralNominalState.Models revision.snapshot model) :
    BranchModels registry (currentContext revision) root declaration checked [(s.root,s.root)] model :=
  branch s registry root declaration checked queries names variables
    (variable_outputs declaration checked.scope outputs) model old current
end Yulang.GeneralDictionaryNonterminalScope
