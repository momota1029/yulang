import Yulang.GeneralRebaseRowLeafWitness288

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 16000000
namespace Yulang.GeneralRebaseRowLeafSlice288
open GeneralRebaseRowChildSource287
open GeneralRebaseRowChildRaw287 (SourceCheck OutputCheck exact_source)
open GeneralRebaseRowParentPacket287 (child plan)
open GeneralRebaseRowParentFrame287 (after effect class_before after_exact)
open GeneralRebaseRowParentInputs287 (inputs_hold)
open GeneralRebaseRowParentOutput287 (outputs_exact)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedSupport233
open GeneralRebaseRowLeafWitness288 (source_exact parent_iff)
open GeneralRebaseLeafOutput288 (Extension output_models output_iff)
open CommonRoleOutermostResolver (All₂)

abbrev prior (choice : Bool) : List (Fact roles) := [.input (plan choice)]

noncomputable abbrev finalFacts (choice : Bool) : List (Fact roles) := .output (effect choice) :: prior choice

theorem input_readback (choice : Bool) : Readback (after choice) [] (plan choice) := by
  intro slot _ test observation head m source
  exact GeneralCanonicalObservations.recorded_sound _ m source.1 (GeneralNominalSupport.head_recorded head)

theorem prior_trusted (choice : Bool) : Trusted (after choice) (prior choice) :=
  .input (plan choice) .source (List.mem_singleton_self _) (input_readback choice)

theorem prefix_exact (choice : Bool) (m : Assignment) :
    SliceModels (after choice) (prior choice) m ↔ SourceCheck m := by
  constructor
  · intro h
    exact (exact_source m).mp h.1
  · intro h
    obtain ⟨valid,sites,_⟩ := (source_exact choice m).mpr h
    refine ⟨valid,sites,?_⟩
    intro fact recorded
    cases List.mem_singleton.mp recorded
    exact inputs_hold choice m valid

theorem class_readback (choice : Bool) : ClassReadback (after choice) (prior choice) (effect choice) := by
  intro site member _
  change site ∈ [GeneralNominalCenters.rootSite raw.seed root] at member
  cases List.mem_singleton.mp member
  constructor
  · rfl
  · change GeneralNominalDemandMerging.All₂ (GeneralNominalDemandMerging.Related _) [some (.source 1)] [some (.source 1)]
    exact .cons ⟨.source 1,.source 1,rfl,rfl,GeneralNominalDemandMerging.source_same _ 1⟩ .nil

theorem extension_iff (choice : Bool) : Extension (after choice) (prior choice) (effect choice) ↔ choice = true := by
  constructor
  · intro certificate
    exact (parent_iff choice).mp certificate.settled
  · intro positive
    exact ⟨prior_trusted choice,List.mem_singleton_self _,List.mem_singleton_self _,class_readback choice,
      (parent_iff choice).mpr positive⟩

theorem slice_exact (choice : Bool) (m : Assignment) :
    SliceModels (after choice) (finalFacts choice) m ↔ OutputCheck m := by
  rw [show finalFacts choice = .output (effect choice) :: prior choice from rfl,output_iff,prefix_exact]
  constructor
  · rintro ⟨source,outputs,_⟩
    exact ⟨source,(outputs_exact choice m).mp outputs⟩
  · rintro ⟨source,equation⟩
    have valid := (after_exact choice m).mpr ⟨source,equation⟩
    exact ⟨source,(outputs_exact choice m).mpr equation,
      (valid.2.2 (effect choice) (List.mem_singleton_self _)).1⟩

theorem same_models (choice : Bool) (m : Assignment) :
    SliceModels (after choice) (finalFacts choice) m ↔ GeneralNominalVersionedJournal232.Models (after choice) m :=
  (slice_exact choice m).trans (after_exact choice m).symm

theorem cannot_use_old_trust (choice : Bool) : ¬ Trusted (after choice) (finalFacts choice) :=
  fun trust => GeneralRebaseRowSettlement287.parent_not_settled choice
    (outputs_settled trust (effect := effect choice) List.mem_cons_self)

end Yulang.GeneralRebaseRowLeafSlice288
