import Yulang.GeneralRebaseOverlap281

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseReplayCriterion281
open GeneralNominalSaturationState (Packet)
open GeneralNominalCenters (Plan)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedInstallation231 (replayPlan)
open GeneralNominalState (Models)
open GeneralRebaseAggregateTags281 (tags fixed versioned versioned_exact)
open GeneralRebaseAggregateLift281 (sourceView)
open GeneralRebaseAggregateCompile281 (compile)
open GeneralRebaseAggregateSupport281 (unique source_read)
open GeneralRebaseActualReplay281 (Baseline baseline_supported replay_exact fixedState fixed_state_exact)
open GeneralRebasePortProjection280 (Supported Extension Respects Project project_extension)
open GeneralRebaseOverlap281 (kept kept_supported project_overlap project_supported)
open GeneralRebaseFixedReplay281 (fixed_unique fixed_apart fixed_isolated)
open GeneralDeclarations GeneralSourceDictionaries

theorem raw_projection (q : Plan roles) (built : compile q.packet = some ws) (m : Assignment) :
    Project (sourceView q.packet) (Models (replayPlan q).packet.context.state) m ↔
      Baseline q.packet m ∧ Respects (kept (sourceView q.packet) ws) m := by
  have fromReplay :
      Project (sourceView q.packet) (Models (replayPlan q).packet.context.state) m ↔
      Project (sourceView q.packet) (Extension (Baseline q.packet) ws) m := by
    constructor <;> rintro ⟨a,agree,valid⟩
    · exact ⟨a,agree,(replay_exact q built a).mp valid⟩
    · exact ⟨a,agree,(replay_exact q built a).mpr valid⟩
  have reads : ∀ row ∈ ws, row.2 ∈ sourceView q.packet := fun _ h => source_read built h
  have support : Supported (sourceView q.packet) (Extension (Baseline q.packet) (kept (sourceView q.packet) ws)) :=
    fun a b eq => and_congr (baseline_supported q.packet a b eq) (kept_supported reads a b eq)
  exact fromReplay.trans ((project_overlap (baseline_supported q.packet) (unique built) reads m).trans
    (project_supported support m))

theorem fixed_projection {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}
    {state : GeneralNominalVersionedJournal232.State roles} (q : Plan roles)
    (reach : GeneralNominalVersionedMixedProgressSplit236.Reachable registry root state)
    (context : q.packet.context.state = GeneralRebaseMixedOwnedTrace277.raw state)
    (built : tags q.packet = some ts) (m : Assignment) :
    Project (sourceView q.packet) (Models (fixedState q.packet (ts.map (fixed q.packet)))) m ↔
      Baseline q.packet m := by
  have exactState :
      Project (sourceView q.packet) (Models (fixedState q.packet (ts.map (fixed q.packet)))) m ↔
      Project (sourceView q.packet) (Extension (Baseline q.packet) (ts.map (fixed q.packet))) m := by
    constructor <;> rintro ⟨a,agree,valid⟩
    · exact ⟨a,agree,(fixed_state_exact ..).mp valid⟩
    · exact ⟨a,agree,(fixed_state_exact ..).mpr valid⟩
  have outside := fixed_apart reach context ts
  exact exactState.trans ((project_extension (baseline_supported q.packet) outside outside
    (fixed_unique built) (fixed_isolated built outside) m).trans
      (project_supported (baseline_supported q.packet) m))

theorem exact_iff_retained {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}
    {state : GeneralNominalVersionedJournal232.State roles} (q : Plan roles)
    (reach : GeneralNominalVersionedMixedProgressSplit236.Reachable registry root state)
    (context : q.packet.context.state = GeneralRebaseMixedOwnedTrace277.raw state)
    (built : tags q.packet = some ts) :
    (∀ m, Project (sourceView q.packet) (Models (replayPlan q).packet.context.state) m ↔
      Project (sourceView q.packet) (Models (fixedState q.packet (ts.map (fixed q.packet)))) m) ↔
    (∀ m, Baseline q.packet m →
      Respects (kept (sourceView q.packet) (ts.map (versioned q.packet))) m) := by
  have compiled : compile q.packet = some (ts.map (versioned q.packet)) := by
    rw [← versioned_exact,built]; rfl
  constructor
  · intro exactBoth m valid
    exact ((raw_projection q compiled m).mp ((exactBoth m).mpr
      ((fixed_projection q reach context built m).mpr valid))).2
  · intro all m
    exact (raw_projection q compiled m).trans
      ((⟨And.left,fun prior => ⟨prior,all m prior⟩⟩ :
          Baseline q.packet m ∧ Respects (kept (sourceView q.packet) (ts.map (versioned q.packet))) m ↔
          Baseline q.packet m).trans (fixed_projection q reach context built m).symm)

end Yulang.GeneralRebaseReplayCriterion281
