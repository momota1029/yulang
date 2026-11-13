import Yulang.GeneralDictionaryNonpointBranch
import Yulang.GeneralDictionaryVariableWhereRequests
import Yulang.GeneralDictionaryRequestSnapshot
import Yulang.GeneralDictionaryActualSchemaScope

/-! Parent BranchModels survive the depth-two nonpoint capture collapse with
arbitrarily many variable-input where clauses. Named clause output schemas remain
allowed. The generated-name scope premise is explicit in this first theorem;
child demand intervals and child Evidence are deliberately separate obligations. -/
namespace Yulang.GeneralDictionaryNonterminalNonpointBranch
open GeneralDictionarySemanticCollapse GeneralDictionarySemanticCollapseAllocation
open GeneralDictionarySemanticCollapseBranch GeneralDictionarySemanticCollapseSchema
open GeneralNominalReobservationSteps GeneralNominalRecursiveInspection
open GeneralNominalAllocation GeneralDeclarations GeneralNominalRecursiveCandidates
open GeneralNominalMaterialization CommonNominalFullCarrier
variable {roles : Roles.RoleDecls} {state : GeneralNominalSaturationState.State roles}
variable {revision : Revision state}

theorem branch (s : Shape revision) (registry : Registry)
    (root : GeneralSourceDictionaries.Occurrence roles) (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (queries : GeneralNominalInspection.queries state.context.state state.context.interpretation declaration = [query s])
    (names : declaration.inputNames = [s.binder]) (variables : GeneralDictionaryVariableWhereRequests.VariableInputs declaration)
    (scope : ∀ entry ∈ (GeneralNominalRecursiveCandidates.generated registry state.context root declaration checked [(s.root,s.root)]).variables,
      entry.name ∉ declaration.outputNames → entry.name = s.binder)
    (model : GeneralNominalCommonBridge.Assignment)
    (old : BranchModels registry state.context root declaration checked [(s.root,s.root)] model)
    (current : GeneralNominalState.Models revision.snapshot model) :
    BranchModels registry (currentContext revision) root declaration checked [(s.root,s.root)] model := by
  have rs := reports s declaration queries
  have projection : ProjectionModels state.context.state
      (inspect state.context.state (query s) (s.root,s.root) none) model := by
    rw [before_exact]
    have h := old.2.1
    rw [rs.1] at h
    exact h
  have oldProp := (GeneralNominalState.extend_models ..).mp old.1 |>.1
  change GeneralNominalState.Models (propagate state.context.state registry root.identity declaration
    (bindings state.context.state (report state.context declaration [(s.root,s.root)]))) model at oldProp
  rw [rs.1] at oldProp
  have prop : GeneralNominalState.Models (propagate state.context.state registry root.identity declaration
    (bindings state.context.state (inspect state.context.state (query s) (s.root,s.root) none))) model := by
    rw [before_exact]; exact oldProp
  refine ⟨GeneralDictionaryNonpointCollapse.private_state s registry root declaration queries names model old.1 current,?_,?_⟩
  · rw [rs.2]
    have h := current_projection s model current projection
    rw [after_exact] at h
    exact h
  · have sameSchema : GeneralNominalRecursiveCandidates.generated registry (currentContext revision) root declaration checked [(s.root,s.root)] =
        GeneralNominalRecursiveCandidates.generated registry state.context root declaration checked [(s.root,s.root)] := by
      exact GeneralDictionaryRequestSnapshot.generated_revision revision registry root declaration checked _ _
    have actual : GeneralDictionaryActualSchema.ActualOnly
        (GeneralNominalRecursiveCandidates.generated registry state.context root declaration checked [(s.root,s.root)]) := by
      unfold GeneralNominalRecursiveCandidates.generated
      exact GeneralDictionaryActualSchema.generated_actual _ _ _
        (GeneralDictionaryVariableWhereRequests.requests_actual _ _ _ _ _ _ variables)
    have materialized := old.2.2
    rw [rs.1] at materialized
    have materialized' : GeneralNominalMaterialization.Models state.context.state declaration
        (oldCapture s registry root.identity declaration)
        (inspect state.context.state (query s) (s.root,s.root) none)
        (GeneralNominalRecursiveCandidates.generated registry state.context root declaration checked [(s.root,s.root)]) model := by
      unfold oldCapture
      rw [before_exact]
      exact materialized
    have result := GeneralDictionaryNonpointBranch.replay s registry root.identity declaration
      (GeneralNominalRecursiveCandidates.generated registry state.context root declaration checked [(s.root,s.root)]) model
      (by simp [names]) scope actual prop materialized'
    rw [sameSchema,rs.2]
    unfold newCapture at result
    rw [after_exact] at result
    exact result
/-- Checked bare-variable where clauses, with no named child outputs, need no
separate generated-name or actual-mode premise. The parent may have arbitrary
associated outputs and arbitrarily many actual emitted children. Child Evidence
is not asserted; the conclusion is the entire parent BranchModels. -/
theorem bare_branch (s : Shape revision) (registry : Registry)
    (root : GeneralSourceDictionaries.Occurrence roles) (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (queries : GeneralNominalInspection.queries state.context.state state.context.interpretation declaration = [query s])
    (names : declaration.inputNames = [s.binder])
    (variables : GeneralDictionaryVariableRequirements.VariableClauses declaration)
    (model : GeneralNominalCommonBridge.Assignment)
    (old : BranchModels registry state.context root declaration checked [(s.root,s.root)] model)
    (current : GeneralNominalState.Models revision.snapshot model) :
    BranchModels registry (currentContext revision) root declaration checked [(s.root,s.root)] model := by
  apply branch s registry root declaration checked queries names
    (fun clause member => (variables clause member).2) _ model old current
  unfold GeneralNominalRecursiveCandidates.generated
  rw [GeneralDictionaryVariableWhereRequests.bare_requests _ _ _ _ _ _ variables]
  exact GeneralDictionaryActualSchemaScope.root_input_name _ _ declaration root checked.scope s.binder names

end Yulang.GeneralDictionaryNonterminalNonpointBranch
