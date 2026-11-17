import Yulang.GeneralDictionaryVersionedGap206AfterStable234
import Yulang.GeneralNominalVersionedMixedEvidenceTransport234
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryMixedGap206Trusted234
open GeneralDictionaryDefaultGap206Source
open GeneralDictionaryVersionedGap206233 GeneralDictionaryVersionedGap206Install233
open GeneralDictionaryVersionedGap206Feedback234 (feedback)
open GeneralNominalVersionedSupport233
open CommonNominalFullCarrier

theorem reachable : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root feedback :=
  GeneralNominalVersionedMixedEmbedding234.reachable GeneralDictionaryVersionedGap206After234.reachable

theorem selected : GeneralNominalVersionedMixedSourceBoundary234.Local registry feedback root (.selected 37 []) :=
  GeneralNominalVersionedMixedEmbedding234.local_iff.mpr GeneralDictionaryVersionedGap206AfterSelected234.selected

theorem evidenceAt : B4SkeletonV8.EvidenceAt (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry feedback root :=
  GeneralNominalVersionedMixedEvidenceTransport234.evidenceAt GeneralDictionaryVersionedGap206AfterSelected234.evidenceAt

theorem readback : Readback feedback [] plan := by
  intro slot member test observation head assignment valid
  exact GeneralCanonicalObservations.recorded_sound snapshot assignment valid.1
    (GeneralNominalSupport.head_recorded head)

theorem input_trusted : Trusted feedback [.input plan] :=
  .input plan .source (List.mem_cons_self ..) readback

theorem class_readback : ClassReadback feedback [.input plan] effect := by
  intro site member alias
  change site ∈ [GeneralNominalCenters.rootSite snapshot.seed root] at member
  cases List.mem_singleton.mp member
  constructor
  · rfl
  · change GeneralNominalDemandMerging.All₂ _ [some (GeneralNominalRecursiveInspection.Origin.source 1)] [some (GeneralNominalRecursiveInspection.Origin.source 1)]
    exact .cons ⟨_,_,rfl,rfl,GeneralNominalDemandMerging.source_same _ _⟩ .nil

theorem settled : PacketSettled feedback plan := terminal_settled (List.mem_cons_self ..) children_empty

theorem output_trusted : Trusted feedback [.output effect,.input plan] :=
  .output effect input_trusted (List.mem_cons_self ..) (List.mem_cons_self ..)
    (List.mem_cons_self ..) class_readback settled

theorem zero_int (assignment) (valid : SliceModels feedback [.output effect,.input plan] assignment) :
    Equivalent (assignment 0).1 (.base .int) := by
  have output := valid.2.2 (.output effect) (List.mem_cons_self ..)
  have effects := (GeneralNominalVersionedEffects231.class_effects_iff ..).mp output.2.2
  have equal := (GeneralNominalCenteredHeadMatEffects.positional_default plan assignment (0 : Fin 1)).mp
    (effects.1 ⟨0,0⟩ (by apply GeneralNominalCenteredHeadOutputs.mem_requests_iff.mpr; exact ⟨_,List.mem_singleton_self _,.refl _,List.mem_singleton_self _⟩) _ rfl)
  have one := scalar assignment valid.1
  exact ⟨subtype_trans equal.1 one.1,subtype_trans one.2 equal.2⟩

end Yulang.GeneralDictionaryMixedGap206Trusted234
