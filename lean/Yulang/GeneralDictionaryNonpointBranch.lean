import Yulang.GeneralDictionaryNonpointCollapse
import Yulang.GeneralDictionaryActualSchema

/-! Terminal depth-two branch replay with arbitrary retained leaf intervals.
Root schemas are actually in actual mode, so old-intersection Fits implies
current-singleton Fits. Point leaves and equivalent endpoints are not premises.
Nonterminal generated children and arbitrary reobservations remain outside scope. -/
namespace Yulang.GeneralDictionaryNonpointBranch
open GeneralDictionarySemanticCollapse GeneralDictionarySemanticCollapseAllocation
open GeneralDictionarySemanticCollapseBranch GeneralDictionarySemanticCollapseSchema
open GeneralNominalReobservationSteps GeneralNominalRecursiveInspection
open GeneralNominalAllocation GeneralDeclarations GeneralNominalRecursiveCandidates
open GeneralNominalMaterialization CommonNominalFullCarrier
variable {roles : Roles.RoleDecls} {state : GeneralNominalSaturationState.State roles}
variable {revision : Revision state}

theorem footprint (s : Shape revision) (registry : Registry) (invocation : Nat)
    (declaration : Declaration) (schema : Schema) (model : GeneralNominalCommonBridge.Assignment)
    (declared : s.binder ∈ declaration.inputNames)
    (scope : ∀ entry ∈ schema.variables, entry.name ∉ declaration.outputNames → entry.name = s.binder)
    (propagated : GeneralNominalState.Models (propagate state.context.state registry invocation declaration
      (bindings state.context.state (inspect state.context.state (query s) (s.root,s.root) none))) model) :
    GeneralDictionaryActualSchema.Footprint declaration (oldCapture s registry invocation declaration)
      (newCapture s registry invocation declaration)
      (inspect state.context.state (query s) (s.root,s.root) none)
      (inspect revision.snapshot (query s) (s.root,s.root) none) schema model := by
  refine ⟨?_,?_,?_⟩
  · intro entry member output
    exact ⟨subtype_refl _,subtype_refl _⟩
  · intro entry member input actual valid
    rw [scope entry member input] at valid ⊢
    exact GeneralDictionaryNonpointCollapse.capture_fits s registry invocation declaration model declared propagated actual valid
  · intro entry member captured present same actual origin known
    rw [after_exact] at present
    have eq := List.mem_singleton.mp present
    subst captured
    refine ⟨⟨s.binder,s.first,some (leaf s)⟩,?_,rfl,known⟩
    rw [before_exact]; simp [beforeReport]

theorem replay (s : Shape revision) (registry : Registry) (invocation : Nat)
    (declaration : Declaration) (schema : Schema) (model : GeneralNominalCommonBridge.Assignment)
    (declared : s.binder ∈ declaration.inputNames)
    (scope : ∀ entry ∈ schema.variables, entry.name ∉ declaration.outputNames → entry.name = s.binder)
    (actual : GeneralDictionaryActualSchema.ActualOnly schema)
    (propagated : GeneralNominalState.Models (propagate state.context.state registry invocation declaration
      (bindings state.context.state (inspect state.context.state (query s) (s.root,s.root) none))) model)
    (materialized : GeneralNominalMaterialization.Models state.context.state declaration
      (oldCapture s registry invocation declaration)
      (inspect state.context.state (query s) (s.root,s.root) none) schema model) :
    GeneralNominalMaterialization.Models revision.snapshot declaration
      (newCapture s registry invocation declaration)
      (inspect revision.snapshot (query s) (s.root,s.root) none) schema model :=
  GeneralDictionaryActualSchema.replay declaration _ _ _ _ schema schema
    (fun _ h => h) (fun _ h => h) model actual
    (footprint s registry invocation declaration schema model declared scope propagated) materialized

/-- Conditional soundness transport for the actual terminal Shape branch. No
point-leaf or endpoint-equivalence assumption remains, and the schema mode
invariant is derived from terminal rootRequests rather than assumed. -/
theorem branch (s : Shape revision) (registry : Registry)
    (root : GeneralSourceDictionaries.Occurrence roles) (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (queries : GeneralNominalInspection.queries state.context.state state.context.interpretation declaration = [query s])
    (names : declaration.inputNames = [s.binder]) (terminal : declaration.requirements = [])
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
      unfold GeneralNominalRecursiveCandidates.generated
      rw [terminal_requests _ _ _ _ _ _ terminal,terminal_requests _ _ _ _ _ _ terminal]
      rfl
    have actual : GeneralDictionaryActualSchema.ActualOnly
        (GeneralNominalRecursiveCandidates.generated registry state.context root declaration checked [(s.root,s.root)]) := by
      unfold GeneralNominalRecursiveCandidates.generated
      rw [terminal_requests _ _ _ _ _ _ terminal]
      exact GeneralDictionaryActualSchema.root_generated_actual _ _ _ _
    have materialized := old.2.2
    rw [rs.1] at materialized
    have materialized' : GeneralNominalMaterialization.Models state.context.state declaration
        (oldCapture s registry root.identity declaration)
        (inspect state.context.state (query s) (s.root,s.root) none)
        (GeneralNominalRecursiveCandidates.generated registry state.context root declaration checked [(s.root,s.root)]) model := by
      unfold oldCapture
      rw [before_exact]
      exact materialized
    have result := replay s registry root.identity declaration
      (GeneralNominalRecursiveCandidates.generated registry state.context root declaration checked [(s.root,s.root)]) model
      (by simp [names]) scope actual prop materialized'
    rw [sameSchema,rs.2]
    unfold newCapture at result
    rw [after_exact] at result
    exact result
end Yulang.GeneralDictionaryNonpointBranch
