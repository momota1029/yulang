import Yulang.GeneralNominalVersionedTransport231
import Yulang.GeneralNominalVersionedEvidence231
set_option backward.isDefEq.respectTransparency false

/-! Fixed-observation reconstruction of candidate preparation and current
frames. Consistency is supplied by a genuine new model, never inferred from
arbitrary added atoms. These are semantic adapters, not operational Steps. -/
namespace Yulang.GeneralNominalVersionedPreparedTransport231
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalRecursiveCandidates (Context arguments report Metadata)
open GeneralNominalRecursiveInspection (bindings Finished)
open GeneralNominalVersionedCandidates231 (inputs Prepared HeadModels)
open GeneralNominalVersionedTransport231 (extendedPlan extendedPacket)
open GeneralDictionaryOrdinaryTransport (extend)

variable (reserved : List Nat) (atoms : List (PresenceNormalForm.Atom Nat))
  (allocated : List GeneralNominalIdentities.Origin)

theorem metadata_iff (registry : Registry) (context : Context) :
    Metadata registry (extend context reserved atoms allocated) ↔ Metadata registry context := Iff.rfl

theorem linked_forward (context : Context) (root : Occurrence roles)
    (linked : GeneralNominalState.Linked context.state root.demand) :
    GeneralNominalState.Linked (extend context reserved atoms allocated).state root.demand := by
  change GeneralNominalState.Linked (GeneralNominalState.extend context.state reserved atoms) root.demand
  exact GeneralNominalRefinements.linked (GeneralNominalRefinements.extended context.state reserved atoms) root.demand linked

theorem located_eq (context : Context) (root : Occurrence roles) :
    arguments (extend context reserved atoms allocated) root = arguments context root := rfl

theorem finished_iff (context : Context) (declaration : Declaration)
    (bounds : List (GeneralNominalInspection.Bounds context.state)) :
    Finished (report (extend context reserved atoms allocated) declaration bounds) ↔
      Finished (report context declaration bounds) := by
  rw [GeneralDictionaryOrdinaryTransport.candidate_report_extended,
    GeneralDictionaryOrdinaryTransport.finished_report]

theorem fresh_owned (context : Context) (registry : Registry) (root : Nat) (captured)
    (owned : GeneralNominalVersionedAllocation231.keys registry root captured ⊆ allocated) :
    GeneralNominalVersionedAllocation231.Fresh (extend context reserved atoms allocated).state registry root captured := by
  intro key member _
  exact List.mem_append_right _ (owned member)

theorem prepared_extended (context : Context) (registry : Registry) (root : Occurrence roles)
    (declaration : Declaration) (bounds : List (GeneralNominalInspection.Bounds context.state))
    (old : Prepared registry context root declaration)
    (located : arguments context (inputs root) = some bounds)
    (owned : GeneralNominalVersionedAllocation231.keys registry root.identity
      (bindings context.state (report context declaration bounds)) ⊆ allocated)
    (common : ∃ model, HeadModels registry (extend context reserved atoms allocated) root declaration bounds model) :
    Prepared registry (extend context reserved atoms allocated) root declaration := by
  obtain ⟨metadata,linked,oldBounds,oldLocated,_,finished,_⟩ := old
  have same := Option.some.inj (oldLocated.symm.trans located)
  subst oldBounds
  refine ⟨metadata,linked_forward reserved atoms allocated context (inputs root) linked,bounds,located,?_,?_,common⟩
  · rw [GeneralDictionaryOrdinaryTransport.candidate_report_extended,
      GeneralDictionaryOrdinaryTransport.bindings_report]
    exact fresh_owned reserved atoms allocated context registry root.identity _ owned
  · exact (finished_iff reserved atoms allocated context declaration bounds).mpr finished

/-- Rebuild an exact current frame in the ordinary-extended snapshot. The
supplied packet witness ensures that added constraints remain satisfiable. -/
theorem frame_extended (registry : Registry) (state : GeneralNominalCenteredSteps.State roles)
    (root : Occurrence roles) (key : Nat) (plan : Plan roles)
    (frame : GeneralNominalVersionedEvidence231.Frame registry state root key plan)
    (owned : GeneralNominalVersionedAllocation231.keys registry root.identity plan.packet.bindings ⊆ allocated)
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
  have ready := prepared_extended reserved atoms allocated plan.packet.context registry root
    plan.packet.declaration plan.packet.bounds old frame.located owned ⟨model,common⟩
  refine ⟨frame.registry_eq,?_,frame.occurrence_eq,frame.key_eq,frame.raw_recorded,
    frame.center_recorded,frame.visible,frame.role_eq,frame.located,?_⟩
  · change extend plan.packet.context reserved atoms allocated =
      extend state.erased.current.context reserved atoms allocated
    rw [frame.context_eq]
  · change Prepared registry (extend state.erased.current.context reserved atoms allocated) root plan.packet.declaration
    simpa only [frame.context_eq] using ready

theorem frame_extended_of_old_holds (registry : Registry) (state : GeneralNominalCenteredSteps.State roles)
    (root : Occurrence roles) (key : Nat) (plan : Plan roles)
    (frame : GeneralNominalVersionedEvidence231.Frame registry state root key plan)
    (owned : GeneralNominalVersionedAllocation231.keys registry root.identity plan.packet.bindings ⊆ allocated)
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalVersionedPlans231.Holds plan model)
    (added : PresenceNormalForm.All CommonNominalFullCarrier.model model atoms) :
    GeneralNominalVersionedEvidence231.Frame registry
      (GeneralNominalCenteredSteps.refresh state (extend state.erased.current.context reserved atoms allocated))
      root key (extendedPlan reserved atoms allocated plan) :=
  frame_extended reserved atoms allocated registry state root key plan frame owned model
    ((GeneralNominalVersionedTransport231.holds_iff reserved atoms allocated plan model).mpr ⟨valid,added⟩)

end Yulang.GeneralNominalVersionedPreparedTransport231
