import Yulang.GeneralVersionedHistoryEvidence310
import Yulang.GeneralNominalVersionedPreparedTransport231
import Yulang.GeneralNominalAllocationSupport

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralVersionedOrdinaryFrame310
open GeneralDeclarations GeneralNominalCenters GeneralSourceDictionaries
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalVersionedTransport231 (extendedPlan extendedPacket)
open GeneralNominalVersionedCandidates231 (Prepared HeadModels)
open GeneralDictionaryOrdinaryTransport (extend)
open GeneralNominalCommonBridge (Assignment)

abbrev Atoms := List (PresenceNormalForm.Atom Nat)

def Supported (before : GeneralNominalState.State) (atoms : Atoms) : Prop :=
  ∀ atom ∈ atoms, GeneralNominalState.atomSources atom ⊆ GeneralNominalState.sources before

theorem fresh (packet : GeneralNominalSaturationState.Packet roles) (atoms : Atoms)
    (prior : GeneralNominalVersionedAllocation231.Fresh packet.context.state packet.registry
      packet.site.occurrence.identity packet.bindings)
    (only : Supported packet.context.state atoms) :
    GeneralNominalVersionedAllocation231.Fresh (extend packet.context [] atoms []).state packet.registry
      packet.site.occurrence.identity packet.bindings := by
  intro origin member used
  have support := GeneralNominalAllocationSupport.extend_sources packet.context.state [] atoms
    (List.Subset.refl _) (by intro _ absent; cases absent) only
  have owned := prior origin member (support used)
  exact List.mem_append_left _ owned

/-- Adding equations on already registered sources never introduces a new
    allocation collision. The current packet still needs one genuine model
    for preparation; the later Certificate theorem quantifies over all models. -/
theorem revalidate {before after : GeneralNominalCenteredSteps.State roles} {plan : Plan roles}
    (old : Frame registry before focus key plan) (atoms : Atoms)
    (only : Supported plan.packet.context.state atoms)
    (current : after.erased.current.context = extend before.erased.current.context [] atoms [])
    (raw : before.erased.current.sites ⊆ after.erased.current.sites)
    (centers : before.sites ⊆ after.sites)
    (m : Assignment) (held : GeneralNominalVersionedPlans231.Holds (extendedPlan [] atoms [] plan) m) :
    Frame registry after focus key (extendedPlan [] atoms [] plan) := by
  have packetContext : (extendedPlan [] atoms [] plan).packet.context = after.erased.current.context := by
    rw [current]
    change extend plan.packet.context [] atoms [] = _
    rw [old.context_eq]
  have common := (GeneralNominalVersionedCandidates231.headModels_packet_iff
    (extendedPacket [] atoms [] plan.packet) m).mpr (GeneralNominalVersionedPlans231.head_models held)
  have oldPrepared : Prepared registry plan.packet.context focus plan.packet.declaration :=
    old.context_eq.symm ▸ old.prepared
  have newPrepared : Prepared registry (extend plan.packet.context [] atoms []) focus plan.packet.declaration := by
    obtain ⟨metadata,linked,bounds,located,sourceFresh,finished,_⟩ := oldPrepared
    have eq := Option.some.inj (located.symm.trans old.located)
    subst bounds
    refine ⟨metadata,GeneralNominalVersionedPreparedTransport231.linked_forward [] atoms []
      plan.packet.context _ linked,plan.packet.bounds,old.located,?_,?_,?_⟩
    · have own : GeneralNominalVersionedAllocation231.Fresh plan.packet.context.state
          plan.packet.registry plan.packet.site.occurrence.identity plan.packet.bindings := by
          rw [old.registry_eq,old.occurrence_eq]
          exact sourceFresh
      rw [GeneralDictionaryOrdinaryTransport.candidate_report_extended,
        GeneralDictionaryOrdinaryTransport.bindings_report]
      simpa only [old.registry_eq,old.occurrence_eq,GeneralNominalSaturationState.Packet.bindings,GeneralNominalPacketSupport.report] using fresh plan.packet atoms own only
    · exact (GeneralNominalVersionedPreparedTransport231.finished_iff [] atoms []
        plan.packet.context plan.packet.declaration plan.packet.bounds).mpr finished
    · refine ⟨m,?_⟩
      change HeadModels plan.packet.registry (extend plan.packet.context [] atoms [])
        plan.packet.site.occurrence plan.packet.declaration plan.packet.bounds m at common
      simpa only [old.registry_eq,old.occurrence_eq] using common
  exact ⟨old.registry_eq,packetContext,old.occurrence_eq,old.key_eq,raw old.raw_recorded,
    centers old.center_recorded,old.visible,old.role_eq,old.located,packetContext ▸ newPrepared⟩

end Yulang.GeneralVersionedOrdinaryFrame310
