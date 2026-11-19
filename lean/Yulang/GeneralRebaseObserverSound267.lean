import Yulang.GeneralRebaseObserverCoverage267

namespace Yulang.GeneralRebaseObserverSound267
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedJournal232 (State Effect Models)
open GeneralNominalCenters (SameInputs Plan)
open GeneralNominalSaturationState (Generated)
open GeneralNominalVersionedInstall232 (install)
open GeneralNominalVersionedMixedKernel234 (Installable)
open GeneralNominalVersionedInstallStep232 (Committed)
open GeneralSourceState (Output)
open GeneralRebaseSourceSurvivor267 (Boundary Encoded declChecked)
open GeneralRebaseHeadProbe267 (atFocus Honest)
open GeneralRebaseSourceObserver267 (Probes proposals proposals_exact installAt installs_exact)
open GeneralRebaseLiveProjection264 (project liveFacts)
open GeneralRebaseStep258 (write)
open GeneralRebaseSourceSelect267 (Guard)

structure Sound (registry : Registry) (state : State roles) (root : Occurrence roles)
 (checked : (Boundary roles).Checked registry) (probes : Probes roles) : Prop where
 metadata : GeneralNominalRecursiveCandidates.Metadata (Encoded registry) state.core.erased.current.context
 honest : ∀ focus, Generated state.core.erased.current root focus →
   Honest (probes.head focus) (atFocus (Encoded registry) state root focus (declChecked checked))
 installFacts : ∀ focus, Generated state.core.erased.current root focus →
   GeneralRebaseInstallCandidates267.Probes (Encoded registry) state (probes.novelty focus) (probes.joint focus)
    (atFocus (Encoded registry) state root focus (declChecked checked))
 diagnostics : ∀ focus, ∀ plan ∈ installAt registry state root focus checked probes,
   Guard registry state focus plan.packet.declaration.id
 mergeFacts : ∀ first ∈ state.core.sites, ∀ last ∈ state.core.sites,
   probes.mergeInputs first last = true → SameInputs (Models state) first last

theorem install_certificate (registry : Registry) (root focus : Occurrence roles) (state : State roles)
 (checked : (Boundary roles).Checked registry)
 (reachable : B4TargetV8.Reachable (Boundary roles) registry root state)
 (probes : Probes roles) (sound : Sound registry state root checked probes)
 (generated : Generated state.core.erased.current root focus)
 (plan : Plan roles) (listed : plan ∈ installAt registry state root focus checked probes) :
 ∃ effect : Effect roles, effect.plan = plan ∧ effect.plan.packet.site.occurrence = focus ∧
 Installable (Encoded registry) state effect ∧ ¬ Committed state effect.plan := by
 obtain ⟨⟨key,kids⟩,chosen,listedAt,yes,obs,choiceOK,novelOK,jointOK⟩ :=
   (GeneralRebaseInstallCandidates267.scan_exact ..).mp listed
 have sameKey := (Prod.mk.inj obs).1
 have selected := GeneralRebaseSourceSelect267.selected_from_verdict registry state root focus checked reachable
   generated sound.metadata (probes.head focus) (sound.honest focus generated) chosen
   (sameKey ▸ sound.diagnostics focus plan listed)
 obtain ⟨effect,reg,atState,same,f,declEq,_⟩ :=
   GeneralRebaseCertifiedPlanEntry267.effect_of_entry registry state root focus checked reachable sound.metadata
     (probes.head focus) (sound.honest focus generated) plan listedAt yes obs selected
 have safeSelection := (f.symm ▸ selected :
   GeneralNominalVersionedMixedSourceBoundary234.Local registry state effect.plan.packet.site.occurrence (.selected key kids))
 rw [←declEq] at safeSelection
 have facts := sound.installFacts focus generated
 have common := facts.jointSound plan listedAt jointOK effect reg atState same
 have novel := GeneralRebaseNoveltyProbe267.sound state (probes.novelty focus) plan (facts.novelSound plan listedAt) novelOK
 exact ⟨effect,same,f,GeneralRebaseSourceInstall267.installable_of_choice registry state root checked reachable
   effect reg atState safeSelection (same.symm ▸ choiceOK) common,same.symm ▸ novel⟩

/-- A listed proposal always has a concrete old-kernel edge from this
actual representative, even if its projection is a stutter. The emitted
fact list is supported by the resulting live journal. -/
theorem witness (registry : Registry) (root : Occurrence roles) (state : State roles)
 (checked : (Boundary roles).Checked registry)
 (reachable : B4TargetV8.Reachable (Boundary roles) registry root state)
 (probes : Probes roles) (sound : Sound registry state root checked probes)
 (owners : List Nat) (pool : List Output)
 (p : GeneralRebaseStep258.Proposal) (listed : p ∈ proposals registry state root checked probes) :
 ∃ after, (Boundary roles).Step registry root state after ∧
 write (project owners pool state) p = project owners pool after ∧ p ⊆ liveFacts after := by
 rcases (proposals_exact ..).mp listed with ⟨plan,onList,rfl⟩ | ⟨⟨a,b⟩,onList,rfl⟩
 · obtain ⟨focus,generated,onFocus⟩ := (installs_exact ..).mp onList
   obtain ⟨effect,same,f,enabled,novel⟩ := install_certificate registry root focus state checked reachable
     probes sound generated plan onFocus
   subst plan
   exact ⟨install state effect,⟨_,f.symm ▸ generated,.install effect enabled novel⟩,
     (GeneralRebaseSourceInstallProjection264.project_install_current registry checked root state reachable
      effect enabled owners pool).symm,
     GeneralRebaseCheckedLocal266.install_proposal_in_live registry checked root state reachable effect enabled⟩
 · have contained := ((GeneralRebaseMergeScan267.linkedPairs_exact ..).mp
       ((GeneralRebaseMergeScan267.scan_exact ..).mp onList).1)
   exact ⟨_,GeneralRebaseMergeScan267.source_step (Encoded registry) state root probes.mergeInputs a b onList
       (sound.mergeFacts a contained.1 b contained.2.1),
     (GeneralRebaseAffectedMerge264.project_merge owners pool state a b).symm,
     GeneralRebaseCheckedLocal266.merge_proposal_in_live state a b⟩

end Yulang.GeneralRebaseObserverSound267
