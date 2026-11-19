import Yulang.GeneralRebaseDynamicRun267

namespace Yulang.GeneralRebaseComputeEffect267
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedJournal232 (State Effect)
open GeneralNominalCenters (Plan)
open GeneralNominalVersionedMixedKernel234 (Installable)
open GeneralNominalVersionedInstallStep232 (Committed)
open GeneralNominalSaturationState (Generated)
open GeneralRebaseSourceSurvivor267 (Encoded Boundary)
open GeneralRebaseSourceObserver267 (installs installs_exact Probes)
open GeneralRebaseObserverSound267 (Sound)

/-- All data of the resulting effect are already named. The existence
certificate supplies proof fields only, not an extracted runtime value. -/
def assemble (registry : Registry) (state : State roles) (plan : Plan roles)
 (certificate : ∃ effect : Effect roles, effect.plan = plan ∧ Installable registry state effect) :
 Effect roles where
 registry := registry
 snapshot := state.core
 plan := plan
 frame := by
   obtain ⟨e,same,enabled⟩ := certificate
   simpa only [same,enabled.registry_eq,enabled.snapshot_eq] using e.frame
 unique := by
   obtain ⟨e,same,enabled⟩ := certificate
   simpa only [same,enabled.registry_eq,enabled.snapshot_eq] using e.unique
 ready := by
   obtain ⟨e,same,enabled⟩ := certificate
   simpa only [same,enabled.snapshot_eq] using e.ready

theorem assemble_eq (registry : Registry) (state : State roles) (plan : Plan roles)
 (certificate) (effect : Effect roles) (same : effect.plan = plan) (enabled : Installable registry state effect) :
 assemble registry state plan certificate = effect :=
 GeneralRebaseSourceInstall267.effect_ext _ _ enabled.registry_eq.symm enabled.snapshot_eq.symm same.symm

def Evidence (registry : Registry) (root : Occurrence roles) (state : State roles) (plan : Plan roles) : Prop :=
 ∃ effect : Effect roles, effect.plan = plan ∧
 Generated state.core.erased.current root effect.plan.packet.site.occurrence ∧
 Installable (Encoded registry) state effect ∧ ¬ Committed state effect.plan

theorem of_list (registry : Registry) (root : Occurrence roles) (state : State roles)
 (checked : (Boundary roles).Checked registry)
 (reachable : B4TargetV8.Reachable (Boundary roles) registry root state)
 (probes : Probes roles) (sound : Sound registry state root checked probes)
 (plan : Plan roles) (listed : plan ∈ installs registry state root checked probes) :
 Evidence registry root state plan := by
 obtain ⟨focus,generated,member⟩ := (installs_exact ..).mp listed
 obtain ⟨effect,same,f,enabled,novel⟩ := GeneralRebaseObserverSound267.install_certificate registry root focus state
   checked reachable probes sound generated plan member
 exact ⟨effect,same,f.symm ▸ generated,enabled,novel⟩

def computed (registry : Registry) (root : Occurrence roles) (state : State roles) (plan : Plan roles)
 (cert : Evidence registry root state plan) : Effect roles :=
 assemble (Encoded registry) state plan (by
   obtain ⟨effect,same,_,enabled,_⟩ := cert
   exact ⟨effect,same,enabled⟩)

theorem computed_valid (registry : Registry) (root : Occurrence roles) (state : State roles) (plan : Plan roles)
 (cert : Evidence registry root state plan) :
 let effect := computed registry root state plan cert
 Generated state.core.erased.current root effect.plan.packet.site.occurrence ∧
 Installable (Encoded registry) state effect ∧ ¬ Committed state effect.plan := by
 obtain ⟨effect,same,generated,enabled,novel⟩ := (show Evidence registry root state plan from cert)
 have eq : computed registry root state plan cert = effect := assemble_eq _ _ _ _ effect same enabled
 rw [eq]
 exact ⟨generated,enabled,novel⟩

end Yulang.GeneralRebaseComputeEffect267
