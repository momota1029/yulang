import Yulang.GeneralNominalVersionedPreparedTransport231

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDepthTwoFrameCarry300
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalRecursiveCandidates (Context arguments report Metadata)
open GeneralNominalRecursiveInspection (bindings Finished)
open GeneralNominalVersionedCandidates231 (inputs Prepared HeadModels)
open GeneralNominalVersionedTransport231 (extendedPlan extendedPacket)
open GeneralDictionaryOrdinaryTransport (extend)
open GeneralNominalVersionedPreparedTransport231 (linked_forward finished_iff)

variable (reserved : List Nat) (atoms : List (PresenceNormalForm.Atom Nat))
  (allocated : List GeneralNominalIdentities.Origin)

theorem prepared_carried (context : Context) (registry : Registry) (root : Occurrence roles)
    (declaration : Declaration) (bounds : List (GeneralNominalInspection.Bounds context.state))
    (old : Prepared registry context root declaration)
    (located : arguments context (inputs root) = some bounds)
    (owned : GeneralNominalVersionedAllocation231.keys registry root.identity
      (bindings context.state (report context declaration bounds)) ⊆ context.state.allocated ++ allocated)
    (common : ∃ model, HeadModels registry (extend context reserved atoms allocated) root declaration bounds model) :
    Prepared registry (extend context reserved atoms allocated) root declaration := by
  obtain ⟨metadata,linked,oldBounds,oldLocated,_,finished,_⟩ := old
  cases Option.some.inj (located.symm.trans oldLocated)
  refine ⟨metadata,linked_forward reserved atoms allocated context (inputs root) linked,bounds,located,?_,?_,common⟩
  · rw [GeneralDictionaryOrdinaryTransport.candidate_report_extended,
      GeneralDictionaryOrdinaryTransport.bindings_report]
    intro key found _
    exact owned found
  · exact (finished_iff reserved atoms allocated context declaration bounds).mpr finished

theorem frame_carried (registry : Registry) (state : GeneralNominalCenteredSteps.State roles)
    (root : Occurrence roles) (key : Nat) (plan : Plan roles)
    (frame : GeneralNominalVersionedEvidence231.Frame registry state root key plan)
    (owned : GeneralNominalVersionedAllocation231.keys registry root.identity plan.packet.bindings ⊆
      plan.packet.context.state.allocated ++ allocated)
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalVersionedPlans231.Holds (extendedPlan reserved atoms allocated plan) model) :
    GeneralNominalVersionedEvidence231.Frame registry
      (GeneralNominalCenteredSteps.refresh state (extend state.erased.current.context reserved atoms allocated))
      root key (extendedPlan reserved atoms allocated plan) := by
  have common := (GeneralNominalVersionedCandidates231.headModels_packet_iff
    (extendedPacket reserved atoms allocated plan.packet) model).mpr (GeneralNominalVersionedPlans231.head_models valid)
  change HeadModels plan.packet.registry (extend plan.packet.context reserved atoms allocated)
    plan.packet.site.occurrence plan.packet.declaration plan.packet.bounds model at common
  rw [frame.registry_eq,frame.occurrence_eq] at common
  have old : Prepared registry plan.packet.context root plan.packet.declaration :=
    frame.context_eq.symm ▸ frame.prepared
  have ready := prepared_carried reserved atoms allocated plan.packet.context registry root
    plan.packet.declaration plan.packet.bounds old frame.located owned ⟨model,common⟩
  refine ⟨frame.registry_eq,?_,frame.occurrence_eq,frame.key_eq,frame.raw_recorded,
    frame.center_recorded,frame.visible,frame.role_eq,frame.located,?_⟩
  · change extend plan.packet.context reserved atoms allocated = extend state.erased.current.context reserved atoms allocated
    rw [frame.context_eq]
  · change Prepared registry (extend state.erased.current.context reserved atoms allocated) root plan.packet.declaration
    simpa only [frame.context_eq] using ready

end Yulang.GeneralDepthTwoFrameCarry300
