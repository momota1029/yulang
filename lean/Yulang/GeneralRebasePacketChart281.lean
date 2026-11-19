import Yulang.GeneralRebaseTermReplay281

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebasePacketChart281
open GeneralNominalCenters (Plan)
open GeneralNominalSaturationState (Packet)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalState (Models atomSources)
open GeneralNominalAllocation (cross cross_exact)
open GeneralNominalRecursiveInspection (selfChecks)
open GeneralNominalVersionedInstallation231 (replayPlan)
open GeneralRebaseAggregateLift281 (sourceView Before)
open GeneralRebaseActualReplay281 (Baseline Checks)
open GeneralRebaseTermAggregate281 (writes atoms atoms_exact reads)
open GeneralRebaseTermCopy281 (kept Respects)
open GeneralRebaseSemanticChart281 (Entails Gain Loss)
open GeneralRebasePortProjection280 (Project)
open PresenceNormalForm (All Atom)

def fact (a : Atom Nat) (m : Assignment) : Prop := a.Holds CommonNominalFullCarrier.model m

def pool (p : Packet roles) : List (Atom Nat) :=
  (cross p.bindings ++ selfChecks p.context.state (GeneralNominalPacketSupport.report p)) ++
    atoms (kept (sourceView p) (writes p false))

theorem supported (p : Packet roles) (a : Atom Nat) (listed : a ∈ pool p) :
    atomSources a ⊆ sourceView p := by
  rcases List.mem_append.mp listed with first | last
  · rcases List.mem_append.mp first with crosses|checks
    · exact GeneralNominalAllocationSupport.cross_sources
        (GeneralNominalAllocationSupport.report_endpoints _ (GeneralNominalPacketSupport.report p)) a crosses
    · exact GeneralNominalAllocationSupport.checks_sources _ _ (fun _ h => h) a checks
  · obtain ⟨row,recorded,found⟩ := List.mem_flatMap.mp last
    obtain ⟨written,inPool⟩ := List.mem_filter.mp recorded
    exact GeneralNominalAllocationSupport.equation_sources row.1 row.2 (of_decide_eq_true inPool)
      (reads p false row written) a found

theorem actual_has (q : Plan roles) (m : Assignment) :
    Project (sourceView q.packet) (Models (replayPlan q).packet.context.state) m ↔
      Models q.packet.context.state m ∧ All CommonNominalFullCarrier.model m (pool q.packet) := by
  rw [GeneralRebaseTermReplay281.actual_project]
  unfold pool Baseline Before Checks
  rw [PresenceNormalForm.all_append,PresenceNormalForm.all_append,cross_exact,atoms_exact]
  constructor
  · rintro ⟨⟨⟨old,crosses⟩,checks⟩,remaining⟩
    exact ⟨old,⟨crosses,checks⟩,remaining⟩
  · rintro ⟨old,⟨crosses,checks⟩,remaining⟩
    exact ⟨⟨⟨old,crosses⟩,checks⟩,remaining⟩

def view (q : Plan roles) (after : Bool) (m : Assignment) : Prop :=
  if after then Project (sourceView q.packet) (Models (replayPlan q).packet.context.state) m
  else Models q.packet.context.state m

theorem relative_complete (q : Plan roles) (m : Assignment) (prior : Models q.packet.context.state m) :
    view q true m ↔ ∀ a ∈ pool q.packet, Entails fact (view q) true a → fact a m := by
  apply GeneralRebaseSemanticChart281.exact_with_base
    (base := Models q.packet.context.state) (obligations := pool q.packet)
  · exact fun v new => ((actual_has q v).mp new).1
  · exact fun _ member => member
  · intro v held
    exact (actual_has q v).trans ⟨And.right,fun h => ⟨held,h⟩⟩
  · exact prior

theorem public_cut_iff (q : Plan roles) :
    Loss (view q) false true ↔ Gain (pool q.packet) fact (view q) false true :=
  GeneralRebaseSemanticChart281.relative_loss_iff (fun _ already => already) (relative_complete q)

end Yulang.GeneralRebasePacketChart281
