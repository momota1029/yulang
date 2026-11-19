import Yulang.GeneralRebasePacketChart281

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebasePacketFootprint281
open GeneralNominalCenters (Plan)
open GeneralNominalSaturationState (Packet)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalState (Models atomSources)
open GeneralNominalCenteredFrame179 (Agree)
open GeneralNominalVersionedInstallation231 (replayPlan)
open GeneralRebaseAggregateLift281 (sourceView)
open GeneralRebasePacketChart281 (pool fact actual_has supported)
open GeneralRebasePortProjection280 (Project)
open GeneralRebaseSemanticChart281 (Entails Loss Gain)
open PresenceNormalForm (All)

def footprint (p : Packet roles) : List Nat := (pool p).flatMap atomSources

theorem footprint_in_source (p : Packet roles) : footprint p ⊆ sourceView p := by
  intro id used
  obtain ⟨atom,listed,inside⟩ := List.mem_flatMap.mp used
  exact supported p atom listed inside

theorem project_through (q : Plan roles) (sub : observed ⊆ sourceView q.packet) (m : Assignment) :
    Project observed (Models (replayPlan q).packet.context.state) m ↔
      Project observed (fun a => Models q.packet.context.state a ∧
        All CommonNominalFullCarrier.model a (pool q.packet)) m := by
  constructor
  · rintro ⟨a,eq,valid⟩
    exact ⟨a,eq,(actual_has q a).mp ⟨a,fun _ _ => rfl,valid⟩⟩
  · rintro ⟨a,eq,valid⟩
    obtain ⟨b,keeps,holds⟩ := (actual_has q a).mpr valid
    exact ⟨b,fun id used => (keeps id (sub used)).trans (eq id used),holds⟩

theorem all_same (p : Packet roles) (need : footprint p ⊆ observed)
    (eq : Agree observed a b) :
    All CommonNominalFullCarrier.model a (pool p) ↔ All CommonNominalFullCarrier.model b (pool p) := by
  have supports := fun atom listed => GeneralNominalCenteredModelExtension.atom_same atom
    (fun id present => eq id (need (List.mem_flatMap.mpr ⟨atom,listed,present⟩)))
  exact ⟨fun h atom listed => (supports atom listed).mp (h atom listed),
    fun h atom listed => (supports atom listed).mpr (h atom listed)⟩

theorem projected_exact (q : Plan roles) (sub : observed ⊆ sourceView q.packet)
    (need : footprint q.packet ⊆ observed) (m : Assignment) :
    Project observed (Models (replayPlan q).packet.context.state) m ↔
      Project observed (Models q.packet.context.state) m ∧
        All CommonNominalFullCarrier.model m (pool q.packet) := by
  rw [project_through q sub]
  constructor
  · rintro ⟨a,eq,prior,atoms⟩
    exact ⟨⟨a,eq,prior⟩,(all_same q.packet need eq).mp atoms⟩
  · rintro ⟨⟨a,eq,prior⟩,atoms⟩
    exact ⟨a,eq,prior,(all_same q.packet need eq).mpr atoms⟩

def view (q : Plan roles) (observed : List Nat) (after : Bool) (m : Assignment) : Prop :=
  if after then Project observed (Models (replayPlan q).packet.context.state) m
  else Project observed (Models q.packet.context.state) m

theorem cut_iff (q : Plan roles) (sub : observed ⊆ sourceView q.packet)
    (need : footprint q.packet ⊆ observed) :
    Loss (view q observed) false true ↔ Gain (pool q.packet) fact (view q observed) false true := by
  apply GeneralRebaseSemanticChart281.relative_loss_iff (base := Project observed (Models q.packet.context.state))
  · exact fun _ h => h
  · apply GeneralRebaseSemanticChart281.exact_with_base (obligations := pool q.packet)
    · exact fun a held => ((projected_exact q sub need a).mp held).1
    · exact fun _ h => h
    · exact fun a prior => (projected_exact q sub need a).trans ⟨And.right,fun all => ⟨prior,all⟩⟩

theorem footprint_cut (q : Plan roles) :
    Loss (view q (footprint q.packet)) false true ↔
      Gain (pool q.packet) fact (view q (footprint q.packet)) false true :=
  cut_iff q (footprint_in_source q.packet) (fun _ h => h)

end Yulang.GeneralRebasePacketFootprint281
