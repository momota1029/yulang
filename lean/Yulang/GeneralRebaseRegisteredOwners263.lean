import Yulang.GeneralNominalSourceOwnerCandidates252

namespace Yulang.GeneralRebaseRegisteredOwners263
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 GeneralNominalVersionedMixedKernel234

/-- Root identity and declaration identity are both part of a table owner.
Using only declaration identity would merge different invocations. -/
def key (plan : Plan roles) : Nat × Nat :=
 (plan.packet.site.occurrence.identity,plan.packet.declaration.id)

def code (plan : Plan roles) : Nat := GeneralNominalIdentities.pair (key plan).1 (key plan).2

theorem code_eq_iff (first last : Plan roles) : code first = code last ↔ key first = key last :=
 by
 constructor
 · intro same
   exact GeneralNominalIdentities.pair_injective same
 · intro same
   exact congrArg (fun pair : Nat × Nat => GeneralNominalIdentities.pair pair.1 pair.2) same

/-- Membership in the actual versioned plan journal has a real installation
origin. The witness keeps the pre-install source path and all installation guards.
No final-state Models or absorption condition is added. -/
theorem registered_origin (registry : Registry) (root : Occurrence roles) (start : State roles)
 (empty : start.plans = []) (state : State roles)
 (path : B4Target.Steps (Step registry root) start state) :
 ∀ plan ∈ state.plans, ∃ before effect,
 B4Target.Steps (Step registry root) start before ∧
 GeneralNominalSaturationState.Generated before.core.erased.current root effect.plan.packet.site.occurrence ∧
 Installable registry before effect ∧ ¬ Committed before effect.plan ∧ plan = effect.plan := by
 induction path with
 | refl =>
   intro plan member
   rw [empty] at member
   cases member
 | @tail before after path step ih =>
   obtain ⟨focus,generated,action⟩ := step
   cases action with
   | administrative action => cases action <;> exact ih
   | refresh | merge => exact ih
   | install effect enabled novel =>
     intro plan member
     rcases List.mem_cons.mp member with rfl | prior
     · exact ⟨before,effect,path,generated,enabled,novel,rfl⟩
     · exact ih plan prior

theorem source_initial_empty (sourceRegistry : Registry) (root : Occurrence roles) (start : State roles)
 (source : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Initial sourceRegistry root start) :
 start.plans = [] := by
 obtain ⟨legacy,_,rfl⟩ := source
 rfl

/-- One source-derived key list covers every plan actually retained in every
reachable versioned journal. Current Generated/Installable/novel premises are
not imposed on those old plans: their historical installation supplies them. -/
theorem source_finite_keys (sourceRegistry : Registry) (root : Occurrence roles) (start : State roles)
 (source : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Initial sourceRegistry root start) :
 ∃ keys : List (Nat × Nat), ∀ state,
 B4Target.Steps ((GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Step sourceRegistry root) start state →
 ∀ plan ∈ state.plans, key plan ∈ keys := by
 obtain ⟨keys,finite⟩ := GeneralNominalSourceOwnerCandidates252.mixed_finite_owners sourceRegistry root start source
 refine ⟨keys,?_⟩
 intro state path plan member
 obtain ⟨before,effect,prior,generated,enabled,novel,rfl⟩ := registered_origin
   (GeneralNominalCenteredHeadAllocEncoding.registry sourceRegistry) root start
   (source_initial_empty sourceRegistry root start source) state path plan member
 exact finite before prior effect generated enabled novel

/-- The exact encoded owner identifiers of currently registered Plans. This
finite selector does not construct representative Plans for future owners. -/
def selected (state : State roles) : List Nat := state.plans.map code

theorem source_finite_codes (sourceRegistry : Registry) (root : Occurrence roles) (start : State roles)
 (source : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Initial sourceRegistry root start) :
 ∃ owners : List Nat, ∀ state,
 B4Target.Steps ((GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Step sourceRegistry root) start state →
 ∀ plan ∈ state.plans, code plan ∈ owners := by
 obtain ⟨keys,finite⟩ := source_finite_keys sourceRegistry root start source
 refine ⟨keys.map (fun pair => GeneralNominalIdentities.pair pair.1 pair.2),?_⟩
 intro state path plan member
 exact List.mem_map.mpr ⟨key plan,finite state path plan member,rfl⟩

theorem source_selection_covered (sourceRegistry : Registry) (root : Occurrence roles) (start : State roles)
 (source : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Initial sourceRegistry root start) :
 ∃ owners : List Nat, ∀ state,
 B4Target.Steps ((GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Step sourceRegistry root) start state →
 selected state ⊆ owners := by
 obtain ⟨owners,finite⟩ := source_finite_codes sourceRegistry root start source
 refine ⟨owners,?_⟩
 intro state path owner member
 obtain ⟨plan,present,rfl⟩ := List.mem_map.mp member
 exact finite state path plan present
end Yulang.GeneralRebaseRegisteredOwners263
