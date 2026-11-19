import Yulang.GeneralRebaseLiveStore282

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseFixedBasis282
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalCenters (Plan)
open GeneralNominalVersionedJournal232 (State)
open GeneralRebaseMixedCounts277 (Actual)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalVersionedMixedProgressSplit236 (Reachable split)
open GeneralRebasePhaseKeys281 (owner source_plans)
open GeneralRebaseMixedOwnedTrace277 (raw)
open GeneralNominalSourceOwnerCandidates252 (mixed_finite_owners)
open GeneralRebaseLiveOwner282 (newest newest_subset)
open GeneralRebaseLiveStore282 (live row_origin live_unique)
open GeneralRebasePrivateKey282 (port)
open GeneralRebaseTermAggregate281 (keys active)
open GeneralRebaseTermCopy281 (Write Respects)
open GeneralPresenceOrderedDedup247 (dedup dedup_subset targets_nodup member_preserved)

abbrev compiledRegistry := GeneralNominalCenteredHeadAllocEncoding.registry

def slots (r : Registry) (seed : Nat) (owners : List (Nat × Nat)) : List Nat :=
  (owners.flatMap fun key => r.declarations.flatMap fun d =>
    if d.id = key.2 then d.inputNames.flatMap fun binder =>
      [port seed key.1 key.2 ⟨binder,false,0⟩,port seed key.1 key.2 ⟨binder,true,0⟩]
    else []).eraseDups

theorem slots_member (r : Registry) (seed : Nat) {owners : List (Nat × Nat)} {id : Nat × Nat}
    (known : id ∈ owners) {d : Declaration} (declared : d ∈ r.declarations) (declId : d.id = id.2)
    {binder : Nat} (used : binder ∈ d.inputNames) (hi : Bool) :
    port seed id.1 id.2 ⟨binder,hi,0⟩ ∈ slots r seed owners := by
  apply List.mem_eraseDups.mpr
  apply List.mem_flatMap.mpr
  refine ⟨id,known,List.mem_flatMap.mpr ⟨d,declared,?_⟩⟩
  rw [ite_eq_left declId]
  refine List.mem_flatMap.mpr ⟨binder,used,?_⟩
  cases hi <;> simp only [List.mem_cons,List.not_mem_nil,or_false,true_or,or_true]

theorem plan_visibility {roles : Roles.RoleDecls} {r : Registry} {root : Occurrence roles}
    {start after : State roles} (init : (boundary roles).Initial r root start)
    (path : B4Target.Steps (Actual r root) start after) :
    ∀ p ∈ after.plans, p.packet.declaration ∈ (compiledRegistry r).declarations := by
  induction path with
  | refl =>
    obtain ⟨old,_,rfl⟩ := init
    intro p listed
    cases listed
  | @tail prior next earlier action ih =>
    rcases split (show Reachable r root prior from ⟨start,init,earlier⟩) action with
        admin|⟨e,enabled,_,rfl⟩
    · cases admin <;> exact ih
    · intro p listed
      rcases List.mem_cons.mp listed with rfl|inPrior
      · change e.plan.packet.declaration ∈ (GeneralNominalCenteredHeadAllocEncoding.registry r).declarations
        rw [← enabled.registry_eq]
        exact e.frame.visible
      · exact ih p inPrior

theorem bindings_member {p : GeneralNominalSaturationState.Packet roles} {key : Nat × Bool}
    (inKeys : key ∈ keys p) : key.1 ∈ p.declaration.inputNames := by
  obtain ⟨name,seen,caseMem⟩ := List.mem_flatMap.mp inKeys
  unfold active at caseMem
  split at caseMem
  · cases caseMem
  · rcases List.mem_cons.mp caseMem with rfl | rest
    · exact seen
    · cases List.mem_singleton.mp rest
      exact seen

theorem exists_common_slots {roles : Roles.RoleDecls} {r : Registry} {root : Occurrence roles} {start : State roles}
    (init : (boundary roles).Initial r root start) :
    ∃ pool : List Nat, pool.Nodup ∧ ∀ s, B4Target.Steps (Actual r root) start s →
      ∀ row ∈ live s, row.1 ∈ pool := by
  obtain ⟨possible,covered⟩ := mixed_finite_owners r root start init
  refine ⟨slots (compiledRegistry r) (raw start).seed possible,GeneralRebaseInstallGrowth277.nodup_names _,?_⟩
  intro s path row listed
  obtain ⟨plan,latest,member⟩ := List.mem_flatMap.mp listed
  have stored := newest_subset _ latest
  have visible := plan_visibility init path plan stored
  have numbered := source_plans init covered path plan stored
  obtain ⟨key,used,same⟩ := row_origin s plan row member
  have finite := slots_member (compiledRegistry r) (raw start).seed numbered visible rfl (bindings_member used) key.2
  have seed := GeneralRebaseLiveOwner282.same_seed (show Reachable r root s from ⟨start,init,path⟩) latest
  rw [same,seed,(GeneralNominalVersionedMixedGrowth234.steps path).seed]
  exact finite

def canonical (s : State roles) : List Write := dedup (live s)

theorem canonical_exact {roles : Roles.RoleDecls} {r : Registry} {root : Occurrence roles}
    {s : State roles} (reach : Reachable r root s) (m : GeneralNominalCommonBridge.Assignment) :
    Respects (canonical s) m ↔ Respects (live s) m := by
  constructor
  · exact fun valid row member => valid row (member_preserved _ (live_unique reach) row member)
  · exact fun valid row member => valid row (dedup_subset _ member)

theorem common_cardinality {roles : Roles.RoleDecls} {r : Registry} {root : Occurrence roles} {start : State roles}
    (init : (boundary roles).Initial r root start) :
    ∃ pool : List Nat, pool.Nodup ∧ ∀ s, B4Target.Steps (Actual r root) start s →
      (canonical s).length ≤ pool.length := by
  obtain ⟨pool,distinct,cover⟩ := exists_common_slots init
  refine ⟨pool,distinct,?_⟩
  intro s path
  rw [← List.length_map Prod.fst]
  apply List.Nodup.length_le_of_subset (targets_nodup _)
  intro id member
  obtain ⟨row,listed,rfl⟩ := List.mem_map.mp member
  exact cover s path row (dedup_subset _ listed)

end Yulang.GeneralRebaseFixedBasis282
