import Yulang.GeneralRebaseAggregateSupport281

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseAggregateLift281
open GeneralNominalSaturationState (Packet)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredFrame179 (Agree)
open GeneralNominalAllocation (Compatible cross cross_exact)
open GeneralNominalVersionedAllocation231 (Fresh propagate propagate_models)
open GeneralRebaseAggregateCompile281 (compile packet_exact)
open GeneralRebaseAggregateSupport281 (endKey unique source_fresh isolated_of_source_apart)
open GeneralRebasePortCopy280 (Copy Apart copy_agrees)
open GeneralRebasePortProjection280 (Project copy_satisfies)
open PresenceNormalForm (All)

def sourceView (p : Packet roles) := GeneralNominalState.sources p.context.state

def targetState (p : Packet roles) :=
  propagate p.context.state p.registry p.site.occurrence.identity p.declaration p.bindings

def Before (p : Packet roles) (m : Assignment) : Prop :=
  GeneralNominalState.Models p.context.state m ∧ Compatible p.bindings m

theorem preserves_cross (p : Packet roles) {m n : Assignment}
    (same : Agree (sourceView p) m n) : Compatible p.bindings m ↔ Compatible p.bindings n := by
  rw [← cross_exact,← cross_exact]
  have tracked := GeneralNominalAllocationSupport.report_endpoints p.context.state (GeneralNominalPacketSupport.report p)
  constructor <;> intro h atom listed
  · exact (GeneralNominalCenteredModelExtension.atom_same atom (fun id present =>
      same id (GeneralNominalAllocationSupport.cross_sources tracked atom listed present))).mp (h atom listed)
  · exact (GeneralNominalCenteredModelExtension.atom_same atom (fun id present =>
      same id (GeneralNominalAllocationSupport.cross_sources tracked atom listed present))).mpr (h atom listed)

theorem copy_exact {p : Packet roles} (compiled : compile p = some ws)
    (apart : Apart ws (sourceView p)) (m : Assignment) :
    GeneralNominalState.Models (targetState p) (Copy ws m) ↔ Before p m := by
  have same := copy_agrees apart m
  have retained : GeneralNominalState.Models p.context.state m ↔ GeneralNominalState.Models p.context.state (Copy ws m) :=
    ⟨GeneralNominalCenteredModelExtension.source_models_same p.context.state same,
      GeneralNominalCenteredModelExtension.source_models_same p.context.state (fun id listed => (same id listed).symm)⟩
  have crossEq := preserves_cross p same
  have merges := (packet_exact p (Copy ws m) compiled).mpr
    (copy_satisfies (unique compiled) (isolated_of_source_apart compiled apart) m)
  rw [targetState,propagate_models]
  exact ⟨fun h => ⟨retained.mpr h.1,crossEq.mpr h.2.1⟩,fun h => ⟨retained.mp h.1,crossEq.mp h.2,merges⟩⟩

theorem lift {p : Packet roles} (compiled : compile p = some ws)
    (visible : p.declaration ∈ p.registry.declarations)
    (fresh : Fresh p.context.state p.registry p.site.occurrence.identity p.bindings)
    (unused : ∀ name ∈ p.declaration.inputNames, ∀ side, endKey p name side ∉ p.context.state.allocated)
    (m : Assignment) (prior : Before p m) :
    ∃ target, Agree (sourceView p) m target ∧ GeneralNominalState.Models (targetState p) target := by
  have apart := source_fresh compiled visible fresh unused
  exact ⟨Copy ws m,copy_agrees apart m,(copy_exact compiled apart m).mpr prior⟩

theorem project {p : Packet roles} (compiled : compile p = some ws)
    (apart : Apart ws (sourceView p)) (visible : Assignment) :
    Project (sourceView p) (GeneralNominalState.Models (targetState p)) visible ↔
      Project (sourceView p) (Before p) visible := by
  constructor
  · rintro ⟨a,agree,held⟩
    have raw := (propagate_models ..).mp held
    exact ⟨a,agree,raw.1,raw.2.1⟩
  · rintro ⟨a,agree,held⟩
    exact ⟨Copy ws a,fun id listed => ((copy_agrees apart a id listed).symm.trans (agree id listed)),
      (copy_exact compiled apart a).mpr held⟩

theorem rows_preserved {p : Packet roles} (_compiled : compile p = some ws)
    (m : Assignment) (id : Nat) : (Copy ws m id).2 = (m id).2 :=
  GeneralRebasePortCopy280.rows_preserved ws m id

end Yulang.GeneralRebaseAggregateLift281
