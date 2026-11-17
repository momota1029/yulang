import Yulang.GeneralDictionaryJournalRefinement228Enable

namespace Yulang.GeneralDictionaryJournalRefinement228Trusted
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryJournalRefinement228Initial
open GeneralDictionaryJournalRefinement228Install
open GeneralNominalCenteredHeadMatStepSupport
open CommonNominalFullCarrier

theorem readback : Readback installed [] plan := by
  intro slot member test observation head m valid
  exact GeneralCanonicalObservations.recorded_sound snapshot m valid.1
    (GeneralNominalSupport.head_recorded head)

theorem input_trusted : Trusted installed [.input plan] :=
  .input plan .source (List.mem_cons_self ..) readback

theorem class_readback : ClassReadback installed [.input plan] effect := by
  intro site member same
  cases List.mem_singleton.mp member
  refine ⟨rfl,?_⟩
  exact .cons ⟨.source 0,.source 0,rfl,rfl,GeneralNominalDemandMerging.source_same _ _⟩ .nil

theorem settled : GeneralNominalSettledSupport.PacketSettled installed.core.erased.current packet := by
  refine ⟨List.mem_cons_self ..,?_⟩
  intro child member
  rw [children_empty] at member
  cases member

theorem output_trusted : Trusted installed [.output effect,.input plan] :=
  .output effect input_trusted (List.mem_cons_self ..) (List.mem_cons_self ..)
    (List.mem_singleton_self _) class_readback settled

theorem output_justified : GeneralNominalCenteredHeadMatStepObservations.Justifies installed
    (fun m => Equivalent (m 4).1 .exactEmpty) := by
  refine ⟨[.output effect,.input plan],output_trusted,?_⟩
  intro m valid
  have output := (valid.2.2 (.output effect) (List.mem_cons_self ..)).1
  change (GeneralNominalCenteredHeadMatPlans.emittedSchema plan).Holds
    (GeneralNominalCenteredHeadMatEffects.variables plan m) m at output
  rw [emitted_schema] at output
  exact output ⟨4,.actual,.primitive .exactEmpty []⟩ (List.mem_singleton_self _)

end Yulang.GeneralDictionaryJournalRefinement228Trusted
