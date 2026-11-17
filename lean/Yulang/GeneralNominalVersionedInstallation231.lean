import Yulang.GeneralNominalVersionedTransport231
import Yulang.GeneralNominalVersionedRefinement231

/-! Concrete additive private-installation/reconstruction for I44.
It appends exactly the versioned cross/merge/self-check atoms and key ownership.
This is a context transformer, not a claimed full journal Step or termination proof. -/
namespace Yulang.GeneralNominalVersionedInstallation231
open GeneralNominalSaturationState (Packet)
open GeneralNominalCenters
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedPlans231

def atoms (packet : Packet roles) : List (PresenceNormalForm.Atom Nat) :=
  (GeneralNominalAllocation.cross packet.bindings ++
    GeneralNominalVersionedAllocation231.merges packet.context.state packet.registry
      packet.site.occurrence.identity packet.declaration packet.bindings) ++
  GeneralNominalRecursiveInspection.selfChecks packet.context.state (GeneralNominalPacketSupport.report packet)

def reserved (packet : Packet roles) : List Nat :=
  GeneralNominalVersionedAllocation231.reserved packet.context.state packet.registry
    packet.site.occurrence.identity packet.bindings

def allocated (packet : Packet roles) : List GeneralNominalIdentities.Origin :=
  GeneralNominalVersionedAllocation231.keys packet.registry packet.site.occurrence.identity packet.bindings

def replayPlan (plan : Plan roles) : Plan roles :=
  GeneralNominalVersionedTransport231.extendedPlan
    (reserved plan.packet) (atoms plan.packet) (allocated plan.packet) plan

theorem atoms_iff (packet : Packet roles) (model : Assignment) :
    PresenceNormalForm.All CommonNominalFullCarrier.model model (atoms packet) ↔ Ordinary packet model := by
  unfold atoms Ordinary
  simp only [PresenceNormalForm.all_append,GeneralNominalAllocation.cross_exact,and_assoc]

theorem replay_holds_iff (plan : Plan roles) (model : Assignment) :
    Holds (replayPlan plan) model ↔ Holds plan model := by
  unfold replayPlan
  rw [GeneralNominalVersionedTransport231.holds_iff,atoms_iff]
  constructor
  · exact And.left
  · intro valid
    exact ⟨valid,valid.2.1.1⟩

theorem replay_private_models (plan : Plan roles) (model : Assignment) :
    GeneralNominalState.Models (replayPlan plan).packet.context.state model ↔
      GeneralNominalState.Models (privateState plan.packet) model := by
  rw [private_models_iff]
  change GeneralNominalState.Models
    (GeneralDictionaryOrdinaryTransport.extendState plan.packet.context.state
      (reserved plan.packet) (atoms plan.packet) (allocated plan.packet)) model ↔ _
  rw [GeneralDictionaryOrdinaryTransport.models_extended,atoms_iff]

theorem replay_source (plan : Plan roles) (slot : Fin plan.packet.context.state.base.slots) :
    (replayPlan plan).packet.context.state.base.source slot = plan.packet.context.state.base.source slot := rfl

theorem replay_seed (plan : Plan roles) :
    (replayPlan plan).packet.context.state.seed = plan.packet.context.state.seed := rfl

theorem replay_center (plan : Plan roles) (name : Nat) :
    GeneralNominalVersionedFrame231.binder (replayPlan plan) name =
      GeneralNominalVersionedFrame231.binder plan name :=
  GeneralNominalVersionedTransport231.binder_eq _ _ _ _ _

theorem replay_children (plan : Plan roles) :
    GeneralNominalVersionedFrame231.children (replayPlan plan).packet =
      GeneralNominalVersionedFrame231.children plan.packet :=
  GeneralNominalVersionedTransport231.children_eq _ _ _ _

theorem replay_known (plan : Plan roles) (name : Nat) :
    GeneralNominalState.Known (replayPlan plan).packet.context.state name ↔
      GeneralNominalState.Known plan.packet.context.state name := Iff.rfl

theorem replay_keys_owned (plan : Plan roles) (member : key ∈ allocated plan.packet) :
    key ∈ (replayPlan plan).packet.context.state.allocated :=
  List.mem_append_right _ member

/-- A previously valid total packet survives exact private installation and
reconstruction, without changing its source dictionary or actual centers. -/
theorem replay_valid (plan : Plan roles) (model : Assignment) (valid : Holds plan model) :
    Holds (replayPlan plan) model := (replay_holds_iff plan model).mpr valid

end Yulang.GeneralNominalVersionedInstallation231
