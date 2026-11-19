import Yulang.GeneralRebaseCompleteHeadProbe267

namespace Yulang.GeneralRebaseInstallCoverage267
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalCenters (Plan)
open GeneralNominalVersionedJournal232 (State Effect)
open GeneralNominalSaturationState (Generated)
open GeneralNominalVersionedInstallStep232 (Committed)
open GeneralNominalVersionedMixedMaterialization237 (Residual)
open GeneralRebaseSourceSurvivor267 (Boundary Encoded declChecked)
open GeneralRebaseHeadProbe267 (atFocus atFocus_exact Honest observation)
open GeneralRebaseCompleteHeadProbe267 (Covered unique_from_complete)
open GeneralRebaseInstallCandidates267 (scan scan_exact)
open GeneralRebaseInstallChecks267 (semanticCommitted choice_exact novel_exact)

structure Covers (registry : Registry) (state : State roles)
 (newSemantics joint : Plan roles → Bool) (entries : List (Plan roles)) : Prop where
 novelty : ∀ plan ∈ entries, (¬ semanticCommitted state plan) → newSemantics plan = true
 joint : ∀ effect : Effect roles, effect.plan ∈ entries →
   effect.registry = registry → effect.snapshot = state.core →
   (∃ model, Residual state effect model) → joint effect.plan = true

/-- Completeness conditional on evidence coverage of the independent semantic
probes. It applies by inversion to all real enabled non-committed installs,
without assuming that they already appeared in a computed list. -/
theorem all_real_installs (registry : Registry) (state : State roles) (root : Occurrence roles)
 (checked : (Boundary roles).Checked registry)
 (reachable : B4TargetV8.Reachable (Boundary roles) registry root state)
 (effect : Effect roles)
 (generated : Generated state.core.erased.current root effect.plan.packet.site.occurrence)
 (enabled : GeneralNominalVersionedMixedKernel234.Installable (Encoded registry) state effect)
 (progress : ¬ Committed state effect.plan)
 (head : Plan roles → Option Bool) (newSemantics joint : Plan roles → Bool)
 (honest : Honest head
   (atFocus (Encoded registry) state root effect.plan.packet.site.occurrence (declChecked checked)))
 (coveredHead : Covered head
   (atFocus (Encoded registry) state root effect.plan.packet.site.occurrence (declChecked checked)))
 (coveredGuards : Covers (Encoded registry) state newSemantics joint
   (atFocus (Encoded registry) state root effect.plan.packet.site.occurrence (declChecked checked))) :
 effect.plan ∈ scan state head newSemantics joint
   (atFocus (Encoded registry) state root effect.plan.packet.site.occurrence (declChecked checked)) := by
 let focus := effect.plan.packet.site.occurrence
 let entries := atFocus (Encoded registry) state root focus (declChecked checked)
 have inReady := GeneralRebaseCandidatePrepared267.includes_real_install (Encoded registry) state root
   (declChecked checked) effect generated enabled
 have listed : effect.plan ∈ entries := (atFocus_exact ..).mpr ⟨inReady,rfl⟩
 have prepared := effect.frame.prepared
 rw [enabled.registry_eq,enabled.snapshot_eq] at prepared
 have knownHead := ((GeneralRebaseCandidatePrepared267.prepared_iff _ _ _ _
   ((GeneralRebaseCandidatePrepared267.ready_exact ..).mp inReady).1).mp prepared)
 have yes : head effect.plan = some true := by
   cases reply : head effect.plan with
   | none => exact False.elim (coveredHead effect.plan listed reply)
   | some value =>
     cases value with
     | false => exact False.elim ((honest.negative effect.plan listed reply) knownHead.2.2)
     | true => rfl
 have unique := effect.unique
 rw [enabled.registry_eq,enabled.snapshot_eq] at unique
 have resolved := unique_from_complete registry state root focus checked reachable generated knownHead.1
   head honest coveredHead unique
 obtain ⟨model,valid⟩ := enabled.common
 have jointOK := coveredGuards.joint effect listed enabled.registry_eq enabled.snapshot_eq
   ⟨model,(GeneralNominalVersionedMixedMaterialization237.installation_models_iff
     checked reachable enabled.registry_eq enabled.snapshot_eq).mp valid⟩
 have noveltyOK : GeneralRebaseNoveltyProbe267.novel state newSemantics effect.plan = true :=
   (GeneralRebaseNoveltyProbe267.flags ..).mpr (((novel_exact ..).mp progress).imp id
     (coveredGuards.novelty effect.plan listed))
 exact (scan_exact ..).mpr ⟨observation effect.plan,resolved,listed,yes,rfl,(choice_exact ..).mpr enabled.choice,noveltyOK,jointOK⟩

end Yulang.GeneralRebaseInstallCoverage267
