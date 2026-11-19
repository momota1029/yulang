import Yulang.GeneralRebaseWholeStore282

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseLiveOwner282
open GeneralNominalCenters (Plan)
open GeneralNominalVersionedJournal232 (State)
open GeneralRebasePhaseKeys281 (owner)
open GeneralRebaseHistorySupport282 (packet_context)
open GeneralRebaseMixedOwnedTrace277 (raw)
open GeneralNominalVersionedMixedProgressSplit236 (Reachable)
open GeneralDeclarations GeneralSourceDictionaries

abbrev Owner := Nat × Nat

def lookup (plans : List (Plan roles)) (key : Owner) : Option (Plan roles) :=
  plans.find? (fun p => owner p == key)

def newest (plans : List (Plan roles)) : List (Plan roles) :=
  ((plans.map owner).eraseDups).filterMap (lookup plans)

theorem lookup_spec {plans : List (Plan roles)} {key : Owner} {p : Plan roles}
    (found : lookup plans key = some p) : p ∈ plans ∧ owner p = key := by
  have yes : (owner p == key) = true := List.find?_some (p := fun q : Plan roles => owner q == key) found
  exact ⟨List.mem_of_find?_eq_some found,beq_iff_eq.mp yes⟩

theorem find_owner {plans : List (Plan roles)} {key : Owner} (used : key ∈ plans.map owner) :
    ∃ p, lookup plans key = some p := by
  unfold lookup
  cases found : plans.find? (fun p => owner p == key) with
  | some p => exact ⟨p,rfl⟩
  | none =>
    obtain ⟨p,listed,eq⟩ := List.mem_map.mp used
    have no := List.find?_eq_none.mp found p listed
    simp [eq] at no

theorem newest_iff (plans : List (Plan roles)) (p : Plan roles) :
    p ∈ newest plans ↔ lookup plans (owner p) = some p := by
  constructor
  · intro inNewest
    obtain ⟨key,_,found⟩ := List.mem_filterMap.mp inNewest
    rw [(lookup_spec found).2]
    exact found
  · intro found
    exact List.mem_filterMap.mpr ⟨owner p,List.mem_eraseDups.mpr
      (List.mem_map.mpr ⟨p,(lookup_spec found).1,rfl⟩),found⟩

theorem newest_subset (plans : List (Plan roles)) : newest plans ⊆ plans :=
  fun p member => (lookup_spec ((newest_iff plans p).mp member)).1

theorem newest_unique {plans : List (Plan roles)} {p q : Plan roles}
    (one : p ∈ newest plans) (two : q ∈ newest plans) (eq : owner p = owner q) : p = q := by
  have first := (newest_iff plans p).mp one
  rw [eq,(newest_iff plans q).mp two] at first
  exact Option.some.inj first.symm

theorem newest_covers {plans : List (Plan roles)} {p : Plan roles} (recorded : p ∈ plans) :
    ∃ q ∈ newest plans, owner p = owner q := by
  obtain ⟨q,found⟩ := find_owner (List.mem_map.mpr ⟨p,recorded,rfl⟩)
  have eq := (lookup_spec found).2
  exact ⟨q,(newest_iff plans _).mpr (eq.symm ▸ found),eq.symm⟩

theorem lookup_first (p : Plan roles) (prior : List (Plan roles)) :
    lookup (p :: prior) (owner p) = some p := by
  simp [lookup,List.find?]

theorem lookup_unchanged (p : Plan roles) (prior : List (Plan roles)) (key : Owner)
    (other : owner p ≠ key) :
    lookup (p :: prior) key = lookup prior key := by
  have no : (owner p == key) = false := Bool.eq_false_iff.mpr (fun yes => other (beq_iff_eq.mp yes))
  simp [lookup,List.find?,no]

theorem same_seed {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}
    {state : State roles} {p : Plan roles} (reach : Reachable registry root state)
    (listed : p ∈ newest state.plans) : p.packet.context.state.seed = (raw state).seed := by
  obtain ⟨prior,_,ctx,seed⟩ := packet_context reach p (newest_subset _ listed)
  exact (congrArg GeneralNominalState.State.seed ctx).trans seed

end Yulang.GeneralRebaseLiveOwner282
