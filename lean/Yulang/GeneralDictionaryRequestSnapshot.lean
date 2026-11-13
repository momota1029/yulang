import Yulang.GeneralDictionaryEmissionRequestIdentity
import Yulang.GeneralDictionaryCollapseReadiness

/-! Input-capture changes preserve materialization requests, not child demands.
The seed, constructors and interpretation are retained by the actual Revision.
No terminal or variable-only restriction is needed for this syntactic fact. -/
namespace Yulang.GeneralDictionaryRequestSnapshot
open GeneralDeclarations GeneralDeclarationDemands GeneralNominalMaterialization
open GeneralNominalAllocation GeneralNominalRecursiveCandidates

theorem canonical_requests (declaration : Declaration)
    (checked : DeclarationChecked constructors roles declaration) (invocation : Nat)
    (old current : Capture) (outputs : current.outputs = old.outputs)
    (allocate : (clause : Clause) → Allocation roles clause) :
    (GeneralCanonicalChildOrder.canonicalEmit invocation declaration checked current allocate).flatMap emissionRequests =
    (GeneralCanonicalChildOrder.canonicalEmit invocation declaration checked old allocate).flatMap emissionRequests := by
  unfold GeneralCanonicalChildOrder.canonicalEmit emitAll
  simp only [List.flatMap_def, List.map_map]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro clause _
  exact GeneralDictionaryEmissionRequestIdentity.emission_requests roles invocation _ _ _ old current outputs _

theorem requests_bindings (state : GeneralNominalState.State) (registry : Registry)
    (root : GeneralSourceDictionaries.Occurrence roles) (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (old current : Bindings) :
    requests state registry root declaration checked current =
      requests state registry root declaration checked old := by
  unfold requests
  rw [canonical_requests declaration checked root.identity
    (capture state registry root.identity declaration.id old)
    (capture state registry root.identity declaration.id current) rfl]

variable {roles : Roles.RoleDecls} {state : GeneralNominalSaturationState.State roles}
variable (revision : GeneralNominalReobservationSteps.Revision state)

theorem requests_revision (registry : Registry)
    (root : GeneralSourceDictionaries.Occurrence roles) (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (old current : Bindings) :
    requests revision.snapshot registry root declaration checked current =
      requests state.context.state registry root declaration checked old := by
  have same : requests revision.snapshot registry root declaration checked current =
      requests state.context.state registry root declaration checked current := rfl
  rw [same, requests_bindings state.context.state registry root declaration checked old current]

theorem generated_revision (registry : Registry)
    (root : GeneralSourceDictionaries.Occurrence roles) (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (old : List (GeneralNominalInspection.Bounds state.context.state))
    (current : List (GeneralNominalInspection.Bounds revision.snapshot)) :
    GeneralNominalRecursiveCandidates.generated registry (GeneralDictionarySemanticCollapseBranch.currentContext revision)
      root declaration checked current =
    GeneralNominalRecursiveCandidates.generated registry state.context root declaration checked old := by
  unfold GeneralNominalRecursiveCandidates.generated GeneralDictionarySemanticCollapseBranch.currentContext
  dsimp only
  rw [requests_revision revision registry root declaration checked]
  rfl

theorem ready_revision (registry : Registry)
    (root : GeneralSourceDictionaries.Occurrence roles) (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (old : List (GeneralNominalInspection.Bounds state.context.state))
    (current : List (GeneralNominalInspection.Bounds revision.snapshot)) :
    RequestReady registry (GeneralDictionarySemanticCollapseBranch.currentContext revision) root declaration checked current ↔
    RequestReady registry state.context root declaration checked old := by
  unfold RequestReady
  rw [generated_revision revision registry root declaration checked old current]
end Yulang.GeneralDictionaryRequestSnapshot
