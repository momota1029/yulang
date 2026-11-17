import Yulang.GeneralDictionaryReachablePacket226

/-! Snapshot/head effect obligations follow from the total packet and installed
live classes. Removing their repeated support does not weaken Models. -/
namespace Yulang.GeneralDictionaryLiveDelta227
open GeneralDeclarations GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal GeneralDictionaryDefaultKernel208
open GeneralDictionarySemanticDelta223 (Depends liveSources live_iff)
open GeneralDictionaryReachablePacket226 (packetSources packet_iff)
variable {roles : Roles.RoleDecls} {state : State roles} {effect : Effect roles}

theorem installation_iff (snapshot : effect.snapshot = state.core) :
    Models (install state effect) model ↔
      Models state model ∧ GeneralNominalCenteredHeadMatStepPackets.Holds effect.plan model ∧
      ∀ prior ∈ effect :: state.effects, prior.Live (installCore state.core effect.plan) model := by
  rw [install_models snapshot]
  constructor
  · rintro ⟨old,packet,_,current,prior⟩
    refine ⟨old,packet,?_⟩
    intro previous member
    rcases List.mem_cons.mp member with rfl | member
    · exact current
    · exact prior previous member
  · rintro ⟨old,packet,live⟩
    have current := live effect (List.mem_cons_self ..)
    have previous : GeneralNominalCenteredHeadMatEffects.ClassEffects state.core
        effect.plan.packet.site.occurrence effect.plan model :=
      GeneralNominalCenteredHeadMatEffects.restrict
        (GeneralNominalCenteredHeadStepEffects.requests_subset_of_sites_aliases
          (before := state.core) (after := installCore state.core effect.plan)
          (fun _ h => List.mem_append_left _ h) (fun _ h => h)) current
    exact ⟨old,packet,⟨GeneralNominalCenteredHeadMatStepPackets.head_equations packet,
      snapshot.symm ▸ previous⟩,current,fun prior member => live prior (List.mem_cons_of_mem _ member)⟩

noncomputable def installDelta (state : State roles) (effect : Effect roles) : List Nat :=
  packetSources effect.plan ++ liveSources (effect :: state.effects) (installCore state.core effect.plan)

/-- Keep every installed live class, without separately protecting snapshots. -/
theorem install_depends
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
    (ground : GeneralNominalGroundAccessibility.GroundRoots context root rootLabels)
    (coverage : GeneralNominalCenteredHeadWFSource.Coverage registry context.interpretation)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (enabled : Installable registry state effect) (depends : Depends state pool) :
    Depends (install state effect) (pool ++ installDelta state effect) := by
  intro a b same
  rw [installation_iff enabled.snapshot_eq,installation_iff enabled.snapshot_eq]
  have old := depends a b (fun n member => same n (List.mem_append_left _ member))
  have packet (one : Models state a) (two : Models state b) := packet_iff source point ground coverage path
    effect.plan (GeneralDictionaryDefaultDepth208.frame enabled) one two
    (fun n member => same n (by simp [installDelta,member]))
  have live := live_iff (effect :: state.effects) (installCore state.core effect.plan)
    (fun n member => same n (by simp [installDelta,member]))
  constructor
  · rintro ⟨valid,held,current⟩
    exact ⟨old.mp valid,(packet valid (old.mp valid)).mp held,live.mp current⟩
  · rintro ⟨valid,held,current⟩
    exact ⟨old.mpr valid,(packet (old.mpr valid) valid).mpr held,live.mpr current⟩

theorem delta_subset (state : State roles) (effect : Effect roles) :
    installDelta state effect ⊆ GeneralDictionaryReachablePacket226.installDelta state effect := by
  intro name member
  rcases List.mem_append.mp member with packet | live
  · simp [GeneralDictionaryReachablePacket226.installDelta,packet]
  · simp only [liveSources,List.flatMap_cons] at live
    rcases List.mem_append.mp live with current | previous
    · simp [GeneralDictionaryReachablePacket226.installDelta,
        GeneralDictionaryDefault214ActualJournal.effectSources,install,current]
    · simp [GeneralDictionaryReachablePacket226.installDelta,liveSources,previous]
end Yulang.GeneralDictionaryLiveDelta227
