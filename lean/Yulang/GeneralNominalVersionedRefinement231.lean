import Yulang.GeneralNominalVersionedPlans231
import Yulang.GeneralNominalRefinements

/-! Source/ownership monotonicity for the new private installation layer.
This is the real refinement certificate; global trace termination is separate. -/
namespace Yulang.GeneralNominalVersionedRefinement231
open GeneralNominalSaturationState (Packet)
open GeneralNominalVersionedPlans231

def installed (packet : Packet roles) :
    GeneralNominalRefinements.Refines packet.context.state (privateState packet) where
  base := (GeneralNominalRefinements.refl packet.context.state).base
  heads := (GeneralNominalRefinements.refl packet.context.state).heads
  nominals := (GeneralNominalRefinements.refl packet.context.state).nominals
  ordinary := fun _ member => List.mem_append_left _ (List.mem_append_left _ member)
  known := fun _ known => known
  reserved := fun _ member => List.mem_append_left _ (List.mem_append_left _ member)
  allocated := fun _ member => List.mem_append_left _ member
  seed := rfl
  constructors := rfl

theorem source_identity (packet : Packet roles) (slot : Fin packet.context.state.base.slots) :
    (privateState packet).base.source slot = packet.context.state.base.source slot := rfl

theorem row_identity (packet : Packet roles) (slot : Fin packet.context.state.base.slots) :
    (privateState packet).base.rowSource slot = packet.context.state.base.rowSource slot := rfl

theorem known_iff (packet : Packet roles) (name : Nat) :
    GeneralNominalState.Known (privateState packet) name ↔
      GeneralNominalState.Known packet.context.state name := Iff.rfl

theorem sources_mono (packet : Packet roles) :
    GeneralNominalState.sources packet.context.state ⊆ GeneralNominalState.sources (privateState packet) :=
  GeneralNominalRefinements.sources (installed packet)

theorem models_restrict (packet : Packet roles) (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models (privateState packet) model) :
    GeneralNominalState.Models packet.context.state model :=
  GeneralNominalRefinements.models (installed packet) model valid

theorem keys_owned (packet : Packet roles) (member : key ∈ GeneralNominalVersionedAllocation231.keys
    packet.registry packet.site.occurrence.identity packet.bindings) :
    key ∈ (privateState packet).allocated :=
  List.mem_append_right _ member

theorem revisit_fresh (packet : Packet roles) :
    GeneralNominalVersionedAllocation231.Fresh (privateState packet)
      packet.registry packet.site.occurrence.identity packet.bindings := by
  intro key member _
  exact keys_owned packet member

theorem preserves_linked (packet : Packet roles) (demand : GeneralSourceState.Demand roles)
    (linked : GeneralNominalState.Linked packet.context.state demand) :
    GeneralNominalState.Linked (privateState packet) demand :=
  GeneralNominalRefinements.linked (installed packet) demand linked

end Yulang.GeneralNominalVersionedRefinement231
