import Yulang.GeneralRebaseFixedOrigin281

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseFixedReplay281
open GeneralNominalSaturationState (Packet)
open GeneralNominalIdentities (Origin source_identity)
open GeneralRebaseAggregateTags281 (Tag tags fixed fixedOrigin fixedWrites versioned versioned_exact)
open GeneralRebaseAggregateCompile281 (compile packet_exact)
open GeneralRebasePortCopy280 (Copy Apart Isolated Unambiguous)
open GeneralRebasePortProjection280 (Supported Extension Project Respects copy_extends project_extension)
open GeneralRebaseAggregateLift281 (Before sourceView targetState)
open GeneralNominalCommonBridge (Assignment)
open GeneralRebaseMixedOwnedTrace277 (raw)
open GeneralNominalVersionedMixedProgressSplit236 (Reachable)
open GeneralDeclarations GeneralSourceDictionaries

theorem fixed_target_same (p : Packet roles) (a b : Tag)
    (same : (fixed p a).1 = (fixed p b).1) :
    a.binder = b.binder ∧ a.upper = b.upper := by
  have key := (source_identity p.context.state.seed _ _).mp same
  have name := congrArg (fun k : Origin => k.2.2.2.1) key
  have side : (if a.upper then (1 : Nat) else 0) = (if b.upper then 1 else 0) :=
    congrArg (fun k : Origin => k.2.2.1) key
  exact ⟨name, by cases x : a.upper <;> cases y : b.upper <;> simp_all⟩

theorem fixed_unique {p : Packet roles} (built : tags p = some ts) :
    Unambiguous (ts.map (fixed p)) := by
  intro a aMember b bMember equalTargets
  obtain ⟨a,prior,rfl⟩ := List.mem_map.mp aMember
  obtain ⟨b,later,rfl⟩ := List.mem_map.mp bMember
  have compiled : compile p = some (ts.map (versioned p)) := by rw [← versioned_exact,built]; rfl
  obtain ⟨sameName,sameDir⟩ := fixed_target_same p a b equalTargets
  have sameVersioned : (versioned p a).1 = (versioned p b).1 := by
    unfold versioned
    rw [sameName,sameDir]
  exact GeneralRebaseAggregateSupport281.unique compiled (versioned p a)
    (List.mem_map.mpr ⟨a,prior,rfl⟩) (versioned p b) (List.mem_map.mpr ⟨b,later,rfl⟩) sameVersioned

theorem fixed_read {p : Packet roles} (built : tags p = some ts) (t : Tag) (prior : t ∈ ts) :
    t.read ∈ sourceView p := by
  have compiled : compile p = some (ts.map (versioned p)) := by rw [← versioned_exact,built]; rfl
  exact GeneralRebaseAggregateSupport281.source_read compiled (List.mem_map.mpr ⟨t,prior,rfl⟩)

theorem fixed_apart {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}
    {p : Packet roles} {state : GeneralNominalVersionedJournal232.State roles} (path : Reachable registry root state)
    (context : p.context.state = raw state) (ts : List Tag) :
    Apart (ts.map (fixed p)) (sourceView p) := by
  intro row member collision
  obtain ⟨t,listed,rfl⟩ := List.mem_map.mp member
  change GeneralNominalIdentities.source p.context.state.seed _ ∈
    GeneralNominalState.sources p.context.state at collision
  rw [context] at collision
  exact GeneralRebaseFixedOrigin281.fixed_absent _ _ t path collision

theorem fixed_isolated {p : Packet roles} (built : tags p = some ts)
    (apart : Apart (ts.map (fixed p)) (sourceView p)) : Isolated (ts.map (fixed p)) := by
  intro row listed collision
  obtain ⟨a,prior,rfl⟩ := List.mem_map.mp listed
  obtain ⟨b,later,same⟩ := List.mem_map.mp collision
  obtain ⟨t,present,rfl⟩ := List.mem_map.mp later
  exact apart _ (List.mem_map.mpr ⟨a,prior,rfl⟩) (same ▸ fixed_read built t present)

theorem before_supported (p : Packet roles) : Supported (sourceView p) (Before p) := by
  intro a b agree
  exact and_congr
    ⟨GeneralNominalCenteredModelExtension.source_models_same p.context.state agree,
      GeneralNominalCenteredModelExtension.source_models_same p.context.state (fun id h => (agree id h).symm)⟩
    (GeneralRebaseAggregateLift281.preserves_cross p agree)

theorem fixed_exact {p : Packet roles} (built : tags p = some ts)
    (apart : Apart (ts.map (fixed p)) (sourceView p)) (target : Assignment) :
    Project (sourceView p) (Extension (Before p) (ts.map (fixed p))) target ↔
      Project (sourceView p) (Before p) target :=
  project_extension (before_supported p) apart apart (fixed_unique built) (fixed_isolated built apart) target

/-- Replacement semantics, not conjunction of prior and current stable writes. -/
theorem replace_versioned {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}
    {p : Packet roles} {state : GeneralNominalVersionedJournal232.State roles} (path : Reachable registry root state)
    (context : p.context.state = raw state) (built : tags p = some ts)
    (versionPrivate : Apart (ts.map (versioned p)) (sourceView p)) (target : Assignment) :
    Project (sourceView p) (GeneralNominalState.Models (targetState p)) target ↔
      Project (sourceView p) (Extension (Before p) (ts.map (fixed p))) target := by
  have compiled : compile p = some (ts.map (versioned p)) := by rw [← versioned_exact,built]; rfl
  exact (GeneralRebaseAggregateLift281.project compiled versionPrivate target).trans
    (fixed_exact built (fixed_apart path context ts) target).symm

end Yulang.GeneralRebaseFixedReplay281
