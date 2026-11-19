import Yulang.GeneralRebaseFixedReplay281

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseActualReplay281
open GeneralNominalSaturationState (Packet)
open GeneralNominalCenters (Plan)
open GeneralRebaseAggregateTags281 (tags fixed versioned versioned_exact)
open GeneralRebaseAggregateLift281 (Before sourceView)
open GeneralRebasePortCopy280 (Write Apart Copy copy_agrees)
open GeneralRebasePortProjection280 (Supported Extension Project project_extension copy_satisfies)
open GeneralRebaseFixedReplay281 (before_supported fixed_apart fixed_unique fixed_isolated)
open GeneralRebaseAggregateSupport281 (unique isolated_of_source_apart)
open GeneralRebaseAggregateCompile281 (compile packet_exact)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalState (State Models Known)
open GeneralNominalVersionedInstallation231 (replayPlan replay_private_models replay_known)
open GeneralNominalVersionedPlans231 (private_models_iff Ordinary)
open GeneralNominalRecursiveInspection (selfChecks)
open PresenceNormalForm (All)
open GeneralDeclarations GeneralSourceDictionaries

def Checks (p : Packet roles) (m : Assignment) : Prop :=
  All CommonNominalFullCarrier.model m (selfChecks p.context.state (GeneralNominalPacketSupport.report p))

def Baseline (p : Packet roles) (m : Assignment) : Prop := Before p m ∧ Checks p m

theorem checks_supported (p : Packet roles) : Supported (sourceView p) (Checks p) := by
  intro a b agree
  have same := fun atom listed => GeneralNominalCenteredModelExtension.atom_same
    (first := a) (last := b) atom (fun id used => agree id (GeneralNominalAllocationSupport.checks_sources
      p.context.state (GeneralNominalPacketSupport.report p) (fun _ h => h) atom listed used))
  exact ⟨fun valid atom listed => (same atom listed).mp (valid atom listed),
         fun valid atom listed => (same atom listed).mpr (valid atom listed)⟩

theorem baseline_supported (p : Packet roles) : Supported (sourceView p) (Baseline p) :=
  fun a b agree => and_congr (before_supported p a b agree) (checks_supported p a b agree)

theorem replay_exact (q : Plan roles) (built : compile q.packet = some ws) (m : Assignment) :
    Models (replayPlan q).packet.context.state m ↔ Extension (Baseline q.packet) ws m := by
  rw [replay_private_models,private_models_iff]
  unfold Ordinary Extension Baseline Before Checks
  rw [packet_exact _ _ built]
  constructor
  · rintro ⟨old,cross,merges,self⟩
    exact ⟨⟨⟨old,cross⟩,self⟩,merges⟩
  · rintro ⟨⟨⟨old,cross⟩,self⟩,merges⟩
    exact ⟨old,cross,merges,self⟩

theorem replay_project (q : Plan roles) (built : compile q.packet = some ws)
    (apart : Apart ws (sourceView q.packet)) (target : Assignment) :
    Project (sourceView q.packet) (Models (replayPlan q).packet.context.state) target ↔
      Project (sourceView q.packet) (Baseline q.packet) target := by
  have criterion : Project (sourceView q.packet) (Models (replayPlan q).packet.context.state) target ↔
      Project (sourceView q.packet) (Extension (Baseline q.packet) ws) target := by
    constructor <;> rintro ⟨m,eq,valid⟩
    · exact ⟨m,eq,(replay_exact q built m).mp valid⟩
    · exact ⟨m,eq,(replay_exact q built m).mpr valid⟩
  exact criterion.trans (project_extension (baseline_supported q.packet) apart apart
    (unique built) (isolated_of_source_apart built apart) target)

def fixedState (p : Packet roles) (writes : List Write) : State :=
  GeneralNominalState.extend p.context.state (writes.map Prod.fst)
    ((GeneralNominalAllocation.cross p.bindings ++
      selfChecks p.context.state (GeneralNominalPacketSupport.report p)) ++
      writes.flatMap fun row => GeneralNominalAllocation.equations row.1 (.var row.2))

theorem fixed_known (q : Plan roles) (writes : List Write) (id : Nat) :
    Known (replayPlan q).packet.context.state id ↔ Known (fixedState q.packet writes) id :=
  replay_known q id

theorem fixed_state_exact (p : Packet roles) (ws : List Write) (m : Assignment) :
    Models (fixedState p ws) m ↔ Extension (Baseline p) ws m := by
  rw [fixedState,GeneralNominalState.extend_models,PresenceNormalForm.all_append,
    PresenceNormalForm.all_append,GeneralNominalAllocation.cross_exact]
  have writeLaw : All CommonNominalFullCarrier.model m
      (ws.flatMap fun row => GeneralNominalAllocation.equations row.1 (.var row.2)) ↔
      GeneralRebasePortProjection280.Respects ws m := by
    constructor
    · intro valid row listed
      apply (GeneralNominalCaptureMerges.equations_exact m row.1 (.var row.2)).mp
      intro atom present
      exact valid atom (List.mem_flatMap.mpr ⟨row,listed,present⟩)
    · intro valid atom contains
      obtain ⟨row,listed,present⟩ := List.mem_flatMap.mp contains
      exact (GeneralNominalCaptureMerges.equations_exact m row.1 (.var row.2)).mpr (valid row listed) atom present
  rw [writeLaw]
  constructor
  · rintro ⟨old,⟨cross,self⟩,merge⟩
    exact ⟨⟨⟨old,cross⟩,self⟩,merge⟩
  · rintro ⟨⟨⟨old,cross⟩,self⟩,merge⟩
    exact ⟨old,⟨cross,self⟩,merge⟩

theorem projected_actual_replacement {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}
    {state : GeneralNominalVersionedJournal232.State roles} (q : Plan roles)
    (path : GeneralNominalVersionedMixedProgressSplit236.Reachable registry root state)
    (context : q.packet.context.state = GeneralRebaseMixedOwnedTrace277.raw state)
    (built : tags q.packet = some ts)
    (versionPrivate : Apart (ts.map (versioned q.packet)) (sourceView q.packet)) (outer : Assignment) :
    Project (sourceView q.packet) (Models (replayPlan q).packet.context.state) outer ↔
      Project (sourceView q.packet) (Models (fixedState q.packet (ts.map (fixed q.packet)))) outer := by
  have compiled : compile q.packet = some (ts.map (versioned q.packet)) := by
    rw [← versioned_exact,built]; rfl
  have apart := fixed_apart path context ts
  have criterion :
      Project (sourceView q.packet) (Models (fixedState q.packet (ts.map (fixed q.packet)))) outer ↔
      Project (sourceView q.packet) (Extension (Baseline q.packet) (ts.map (fixed q.packet))) outer := by
    constructor <;> rintro ⟨m,eq,valid⟩
    · exact ⟨m,eq,(fixed_state_exact ..).mp valid⟩
    · exact ⟨m,eq,(fixed_state_exact ..).mpr valid⟩
  exact (replay_project q compiled versionPrivate outer).trans
    (criterion.trans (project_extension (baseline_supported q.packet) apart apart
      (fixed_unique built) (fixed_isolated built apart) outer)).symm

end Yulang.GeneralRebaseActualReplay281
