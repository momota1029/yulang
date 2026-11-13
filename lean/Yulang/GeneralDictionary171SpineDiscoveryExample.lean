import Yulang.GeneralDictionary171SpineDiscovery
import Yulang.GeneralDictionary171SpineExample

/-! The nominal/named-output fixture is recovered from real finished request
inspection, without using its pre-existing observed-output certificate. -/
namespace Yulang.GeneralDictionary171SpineDiscoveryExample
open GeneralDeclarations GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralDictionary171SpineDiscovery GeneralDictionary171InspectionObservation
open GeneralDictionary170NamedSpineExample

def input : Input context root declaration where
  terminal := shape.terminal
  role := shape.role
  slot := shape.slot
  arity := shape.arity
  names := shape.names
  distinct := shape.distinct
  inputs := shape.inputs
  bounds := shape.bounds
  spine := shape.spine
  query := shape.query
  located := shape.located
  defined := shape.defined

theorem point_descriptors : PointDescriptors source := by
  intro slot descriptor recorded
  by_cases zero : slot = 0
  · subst slot
    have same := Option.some.inj recorded
    subst descriptor
    exact ⟨3,fun _ => (1 : Fin 2),rfl⟩
  · simp [source,GeneralDictionaryFiniteObservedExample.state,zero] at recorded

theorem closed_request : Closed GeneralDictionaryFiniteObservedExample.query := by
  apply Closed.nominal
  intro query member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl <;> exact .scalar _

/-- This runs actual inspect at slot0; it does not invert an assumed Tree. -/
theorem finished_request : Finished (inspect source GeneralDictionaryFiniteObservedExample.query
    ((0 : Fin 2),0) (some (.source 0))) := by
  unfold Finished
  decide +kernel

theorem tested_requests : RequestsFinished registry context root declaration checked input := by
  intro request member
  rw [GeneralDictionaryObservedScalarRequests.requests_root _ _ _ _ _ _ (by intro c h; cases h)] at member
  have same := List.mem_singleton.mp member
  subst request
  refine ⟨(0 : Fin 2),rfl,?_,?_,?_⟩
  · rw [GeneralDictionaryFiniteObservedExample.translation]
    exact closed_request
  · rw [GeneralDictionaryFiniteObservedExample.translation]
    exact finished_request
  · exact GeneralDictionary171LocalInspectionObservation.of_global source point_descriptors _

def discovered_node : GeneralDictionary171SpineCoverage.Node registry start root :=
  node registry start root declaration (by simp) checked input tested_requests

theorem discovered_evidence :
    GeneralNominalState.Models source GeneralDictionaryFiniteObservedExample.model ∧
    (∀ assignment, GeneralNominalState.Models source assignment →
      GeneralDictionaryRecursiveEvidence.Evidence registry context assignment root (.node declaration.id [])) :=
  ⟨GeneralDictionaryFiniteObservedExample.state_models,
    uniform_evidence registry context root declaration (by simp) checked input tested_requests metadata⟩

/-- Successful real output inspection now constructs the local certificate
which the old four-constructor language provably cannot express. -/
theorem inspected_strict_node :
    Nonempty (GeneralDictionary171SpineCoverage.Node registry start root) ∧
    ¬ Nonempty (GeneralDictionary170NamedCoverage.Node registry start root) :=
  ⟨⟨discovered_node⟩,no_current_local_node⟩
end Yulang.GeneralDictionary171SpineDiscoveryExample
