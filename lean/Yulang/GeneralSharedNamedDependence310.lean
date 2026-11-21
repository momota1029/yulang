import Yulang.GeneralSharedNamedEvidence310

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 25000
set_option maxHeartbeats 13500000
namespace Yulang.GeneralSharedNamedDependence310
open GeneralSharedNamedSource310 (root registry associated impl leafBody lowRule highRule lowOut highOut)
open GeneralSharedNamedPlan310 (z loSite hiSite loSig hiSig)
open GeneralSharedNamedInstall310 (after)
open GeneralSharedNamedEvidence310 (parentPlan parent_certificate leaf_certificate root_evidence payload)
open GeneralSharedNamedLeaf310 (Side site)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Equivalent subtype_trans)
open GeneralDeclarationExamples (roles)
open GeneralNominalVersionedFrame231 (binder clauseChild)
open GeneralNominalCenteredHeadMatEffects (compileBody)
open GeneralDictionaryAssociatedProvenance (Supplies)

theorem actual_children (side : Side) :
    GeneralNominalSaturationState.Generated after.core.erased.current root (site side).occurrence := by
  cases side
  · exact GeneralSharedNamedInstall310.actual_low
  · exact GeneralSharedNamedInstall310.actual_high

theorem child_body (side : Side) :
    compileBody (GeneralSharedNamedLeaf310.plan side) (.explicit leafBody) = some (.primitive (.scalar .int) []) := by
  cases side <;> rfl

theorem parent_body :
    compileBody parentPlan (.explicit associated) = some (.variable 5) := rfl

theorem parent_receiver (side : Side) :
    (site side).occurrence =
      if side = .low then clauseChild parentPlan.packet lowRule loSig
      else clauseChild parentPlan.packet highRule hiSig := by
  cases side
  · simp only [ite_true]
    exact (GeneralNominalVersionedTransport231.clauseChild_eq _ _ _ _ lowRule loSig).symm
  · simp only [show Side.high ≠ .low from by decide,ite_false]
    exact (GeneralNominalVersionedTransport231.clauseChild_eq _ _ _ _ highRule hiSig).symm

theorem actual_shared_output (side : Side) (m : Assignment) (valid : Models after m) :
    Equivalent (m 1).1 (.base .int) ∧
      GeneralDictionaryDefaultEvidence204.OutputWitness (GeneralSharedNamedLeaf310.plan side) m ⟨1,z⟩ := by
  refine ⟨valid.1.1.1.2.1 (1 : Fin 2) (.base .int) rfl,?_⟩
  apply (leaf_certificate side m valid).outputs
  rw [GeneralSharedNamedLeaf310.named_requests]
  exact List.mem_singleton_self _

/-- A shared named receiver may agree with an explicit externally requested
    parent output without being used as either child's input observation. -/
theorem same_model_bundle (m : Assignment) (valid : Models after m) :
    GeneralDictionaryDefaultEvidence204.OutputWitness parentPlan m ⟨0,1⟩ ∧
    (∀ side, GeneralNominalSaturationState.Generated after.core.erased.current root (site side).occurrence ∧
      GeneralDictionaryDefaultEvidence204.OutputWitness (GeneralSharedNamedLeaf310.plan side) m ⟨1,z⟩ ∧
      Equivalent (m 1).1 (m z).1) ∧
    (boundary roles).Evidence registry after m root payload := by
  refine ⟨GeneralSharedNamedEvidence310.output m valid,?_,root_evidence m valid⟩
  intro side
  exact ⟨actual_children side,(actual_shared_output side m valid).2,
    GeneralSharedNamedInstall310.installed_equality m valid⟩

theorem makes_no_input_claim (side : Side) :
    (∀ i, (site side).occurrence.demand.arguments i = (1,1)) ∧
    (site side).occurrence.demand.outputs = [⟨1,z⟩] ∧ z ≠ 1 := by
  refine ⟨GeneralSharedNamedLeaf310.args side,GeneralSharedNamedLeaf310.named_requests side,?_⟩
  decide +kernel

end Yulang.GeneralSharedNamedDependence310
