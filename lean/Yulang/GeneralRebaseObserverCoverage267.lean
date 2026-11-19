import Yulang.GeneralRebaseSourceObserver267

namespace Yulang.GeneralRebaseObserverCoverage267
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalCenters (SameInputs)
open GeneralNominalSaturationState (Generated)
open GeneralSourceState (Output)
open GeneralRebaseSourceSurvivor267 (Boundary Encoded declChecked)
open GeneralRebaseHeadProbe267 (atFocus Honest)
open GeneralRebaseSourceObserver267 (Probes proposals proposals_exact installAt installs_exact)
open GeneralRebaseLiveProjection264 (project)
open GeneralRebaseStep258 (write)
open GeneralRebaseCheckedLocal266 (affectedProposal)
open GeneralRebaseMultiSelection263 (proposal ofPlan)

structure Covers (registry : Registry) (state : State roles) (root : Occurrence roles)
 (checked : (Boundary roles).Checked registry) (probes : Probes roles) : Prop where
 honest : ∀ focus, Generated state.core.erased.current root focus →
   Honest (probes.head focus) (atFocus (Encoded registry) state root focus (declChecked checked))
 totalHead : ∀ focus, Generated state.core.erased.current root focus →
   GeneralRebaseCompleteHeadProbe267.Covered (probes.head focus)
    (atFocus (Encoded registry) state root focus (declChecked checked))
 installFacts : ∀ focus, Generated state.core.erased.current root focus →
   GeneralRebaseInstallCoverage267.Covers (Encoded registry) state (probes.novelty focus) (probes.joint focus)
    (atFocus (Encoded registry) state root focus (declChecked checked))
 mergeFacts : ∀ first ∈ state.core.sites, ∀ last ∈ state.core.sites,
   SameInputs (Models state) first last → probes.mergeInputs first last = true

/-- Conditional completeness in the forward direction for *all* strict old
source steps, not only installs already present in a caller-supplied table. -/
theorem emits_strict (registry : Registry) (root : Occurrence roles) (state after : State roles)
 (checked : (Boundary roles).Checked registry)
 (reachable : B4TargetV8.Reachable (Boundary roles) registry root state)
 (probes : Probes roles) (covered : Covers registry state root checked probes)
 (owners : List Nat) (pool : List Output)
 (step : (Boundary roles).Step registry root state after)
 (changed : project owners pool after ≠ project owners pool state) :
 ∃ p ∈ proposals registry state root checked probes,
 write (project owners pool state) p = project owners pool after := by
 rcases GeneralRebaseStrictSourceCases267.strict_inversion registry root state after reachable step
   owners pool changed with ⟨effect,generated,enabled,novel,rfl⟩ | ⟨a,b,one,two,generated,matching,openPair,rfl⟩
 · let focus := effect.plan.packet.site.occurrence
   have atSource : effect.plan ∈ installAt registry state root focus checked probes :=
     GeneralRebaseInstallCoverage267.all_real_installs registry state root checked reachable effect generated enabled novel
       (probes.head focus) (probes.novelty focus) (probes.joint focus)
       (covered.honest focus generated) (covered.totalHead focus generated) (covered.installFacts focus generated)
   have member := (installs_exact ..).mpr ⟨focus,generated,atSource⟩
   refine ⟨proposal state.core (ofPlan effect.plan),(proposals_exact ..).mpr (Or.inl ⟨effect.plan,member,rfl⟩),?_⟩
   exact (GeneralRebaseSourceInstallProjection264.project_install_current registry checked root state reachable
      effect enabled owners pool).symm
 · have member := GeneralRebaseMergeScan267.actual_covered state root probes.mergeInputs a b one two
     generated openPair matching (covered.mergeFacts a one b two)
   refine ⟨affectedProposal state a b,(proposals_exact ..).mpr (Or.inr ⟨(a,b),member,rfl⟩),?_⟩
   exact (GeneralRebaseAffectedMerge264.project_merge owners pool state a b).symm

end Yulang.GeneralRebaseObserverCoverage267
