import Yulang.GeneralRebaseTermAggregate281

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseTermReplay281
open GeneralNominalSaturationState (Packet)
open GeneralNominalCenters (Plan)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedPlans231 (Ordinary private_models_iff)
open GeneralNominalVersionedInstallation231 (replayPlan replay_private_models replay_known)
open GeneralNominalState (Models Known State extend extend_models)
open GeneralRebaseAggregateLift281 (sourceView Before)
open GeneralRebaseActualReplay281 (Baseline Checks baseline_supported)
open GeneralRebasePortProjection280 (Project)
open GeneralRebaseTermAggregate281 (writes address expression atoms atoms_exact unique reads versioned_atoms)
open GeneralRebaseTermCopy281 (Write Respects kept project_exact)
open GeneralRebaseMixedOwnedTrace277 (raw)
open GeneralNominalVersionedMixedProgressSplit236 (Reachable)
open GeneralNominalRecursiveInspection (selfChecks)
open GeneralDeclarations GeneralSourceDictionaries

def fixedState (p : Packet roles) : State :=
  extend p.context.state ((writes p true).map Prod.fst)
    ((GeneralNominalAllocation.cross p.bindings ++
      selfChecks p.context.state (GeneralNominalPacketSupport.report p)) ++ atoms (writes p true))

theorem actual_models (q : Plan roles) (m : Assignment) :
    Models (replayPlan q).packet.context.state m ↔ Baseline q.packet m ∧ Respects (writes q.packet false) m := by
  rw [replay_private_models,private_models_iff]
  unfold Ordinary
  rw [← versioned_atoms,atoms_exact]
  constructor
  · rintro ⟨old,cross,merges,self⟩; exact ⟨⟨⟨old,cross⟩,self⟩,merges⟩
  · rintro ⟨⟨⟨old,cross⟩,self⟩,merges⟩; exact ⟨old,cross,merges,self⟩

theorem fixed_models (p : Packet roles) (m : Assignment) :
    Models (fixedState p) m ↔ Baseline p m ∧ Respects (writes p true) m := by
  rw [fixedState,extend_models,PresenceNormalForm.all_append,PresenceNormalForm.all_append,
    GeneralNominalAllocation.cross_exact,atoms_exact]
  constructor
  · rintro ⟨old,⟨cross,self⟩,rows⟩; exact ⟨⟨⟨old,cross⟩,self⟩,rows⟩
  · rintro ⟨⟨⟨old,cross⟩,self⟩,rows⟩; exact ⟨old,⟨cross,self⟩,rows⟩

theorem actual_project (q : Plan roles) (m : Assignment) :
    Project (sourceView q.packet) (Models (replayPlan q).packet.context.state) m ↔
      Baseline q.packet m ∧ Respects (kept (sourceView q.packet) (writes q.packet false)) m := by
  have first : Project (sourceView q.packet) (Models (replayPlan q).packet.context.state) m ↔
      Project (sourceView q.packet) (fun a => Baseline q.packet a ∧ Respects (writes q.packet false) a) m := by
    constructor <;> rintro ⟨a,eq,h⟩
    · exact ⟨a,eq,(actual_models q a).mp h⟩
    · exact ⟨a,eq,(actual_models q a).mpr h⟩
  exact first.trans (project_exact (baseline_supported q.packet) (unique q.packet false) (reads q.packet false) m)

theorem fixed_outside {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}
    {state : GeneralNominalVersionedJournal232.State roles} {p : Packet roles}
    (reach : Reachable registry root state) (context : p.context.state = raw state) :
    ∀ row ∈ writes p true, row.1 ∉ sourceView p := by
  intro row listed seen
  obtain ⟨key,_,rfl⟩ := List.mem_map.mp listed
  change GeneralNominalIdentities.source p.context.state.seed
    (GeneralRebaseAggregateTags281.fixedOrigin p.site.occurrence.identity p.declaration.id ⟨key.1,key.2,0⟩) ∈
      GeneralNominalState.sources p.context.state at seen
  rw [context] at seen
  exact GeneralRebaseFixedOrigin281.fixed_absent _ _ _ reach seen

theorem fixed_project {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}
    {state : GeneralNominalVersionedJournal232.State roles} (p : Packet roles)
    (reach : Reachable registry root state) (context : p.context.state = raw state) (m : Assignment) :
    Project (sourceView p) (Models (fixedState p)) m ↔ Baseline p m := by
  have first : Project (sourceView p) (Models (fixedState p)) m ↔
      Project (sourceView p) (fun a => Baseline p a ∧ Respects (writes p true) a) m := by
    constructor <;> rintro ⟨a,eq,h⟩
    · exact ⟨a,eq,(fixed_models p a).mp h⟩
    · exact ⟨a,eq,(fixed_models p a).mpr h⟩
  exact first.trans ((project_exact (baseline_supported p) (unique p true) (reads p true) m).trans
    ⟨And.left,fun h => ⟨h,fun row found => by
      obtain ⟨listed,inside⟩ := List.mem_filter.mp found
      exact False.elim (fixed_outside reach context row listed (of_decide_eq_true inside))⟩⟩)

theorem replacement_iff {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}
    {state : GeneralNominalVersionedJournal232.State roles} (q : Plan roles)
    (reach : Reachable registry root state) (context : q.packet.context.state = raw state) :
    (∀ m, Project (sourceView q.packet) (Models (replayPlan q).packet.context.state) m ↔
          Project (sourceView q.packet) (Models (fixedState q.packet)) m) ↔
    (∀ m, Baseline q.packet m → Respects (kept (sourceView q.packet) (writes q.packet false)) m) := by
  constructor
  · intro equal a valid
    exact ((actual_project q a).mp ((equal a).mpr ((fixed_project q.packet reach context a).mpr valid))).2
  · intro consequence a
    exact (actual_project q a).trans ((show _ ↔ Baseline q.packet a from
        ⟨And.left,fun current => ⟨current,consequence a current⟩⟩).trans (fixed_project q.packet reach context a).symm)

theorem same_known (q : Plan roles) (id : Nat) :
    Known (replayPlan q).packet.context.state id ↔ Known (fixedState q.packet) id :=
  replay_known q id

end Yulang.GeneralRebaseTermReplay281
