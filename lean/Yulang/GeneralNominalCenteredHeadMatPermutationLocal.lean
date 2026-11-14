import Yulang.GeneralNominalCenteredHeadMatPermutationLedger

set_option backward.isDefEq.respectTransparency false

/-! Fixed-target observations retain literal demand and child identities.
Only the historical plan and effect representation changes. -/
namespace Yulang.GeneralNominalCenteredHeadMatPermutationLocal
open GeneralDeclarations GeneralSourceDictionaries GeneralRegistryReordering GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal (State Models)
open GeneralNominalCenteredHeadMatStepLocal
open GeneralNominalCenteredHeadMatPermutationRaw
open GeneralNominalCenteredHeadMatPermutationPlans (Pair)
open GeneralNominalCenteredHeadMatPermutationLedger
open GeneralNominalCenteredHeadOutputs (Frame)
open GeneralNominalCenteredHeadStepObservationPermutation (survivor unique inspection_pending)
variable {roles : Roles.RoleDecls}

theorem frame_counterpart {first last : GeneralNominalCenteredSteps.State roles} (same : Core first last) (order : Reorders registry otherRegistry)
    (roleEq : registry.roles = roles) (frame : Frame registry first root key plan) :
    ∃ other, Frame otherRegistry last root key other ∧ Pair plan other := by
  have packetOrder : Reorders plan.packet.registry otherRegistry := frame.registry_eq ▸ order
  obtain ⟨other,reg,ctx,visible,matched,rebased⟩ := GeneralNominalCenteredPermutationCounterparts.counterpart plan
    packetOrder (frame.registry_eq ▸ roleEq) same.current.context frame.context_eq (frame.registry_eq ▸ frame.visible)
  have packetRoot : other.packet.site.occurrence = root :=
    (congrArg GeneralNominalDemandMerging.Site.occurrence matched.packet.site).symm.trans frame.occurrence_eq
  have ready : GeneralNominalCenteredHeadCandidates.Prepared otherRegistry last.erased.current.context root other.packet.declaration := by
    have old : GeneralNominalCenteredHeadCandidates.Prepared plan.packet.registry plan.packet.context root plan.packet.declaration := by
      simpa only [frame.registry_eq,frame.context_eq] using frame.prepared
    simpa only [GeneralNominalCenteredHeadCandidates.prepared_headReady,reg,ctx]
      using (matched.ready (GeneralNominalCenteredHeadCandidates.inputs root)).mp old
  have located : GeneralNominalRecursiveCandidates.arguments other.packet.context
      (GeneralNominalCenteredHeadCandidates.inputs root) = some other.packet.bounds := by
    have old : GeneralNominalRecursiveCandidates.arguments plan.packet.context plan.packet.site.occurrence = some plan.packet.bounds :=
      frame.occurrence_eq ▸ frame.located
    change GeneralNominalRecursiveCandidates.arguments other.packet.context root = some other.packet.bounds
    simpa only [packetRoot] using matched.located.mp old
  refine ⟨other,⟨reg,ctx,packetRoot,matched.packet.identity.symm.trans frame.key_eq,?_,?_,visible,
    matched.declaration.role.symm.trans frame.role_eq,located,ready⟩,
    GeneralNominalCenteredHeadMatPermutationPlans.of_rebased rebased matched.input (frame.registry_eq ▸ roleEq)⟩
  · rw [← matched.packet.site]; exact (same.current.sites _).mp frame.raw_recorded
  · rw [← matched.input]; exact (same.centers _).mp frame.center_recorded

variable {relation : Plan roles → Plan roles → Prop} {first last : State roles}

theorem cyclic (same : Related relation first last) (origin) :
    GeneralNominalCenteredHeadMatStepCycles.Cyclic first origin ↔ GeneralNominalCenteredHeadMatStepCycles.Cyclic last origin :=
  GeneralNominalCenteredHeadMatStepCycles.full_models_only (funext (fun model => propext (same.models model)))

theorem chosen_head_forward (same : Related relation first last) (registry : Registry) (roleEq : registry.roles = roles)
    (chosen : ChosenHead registry first root key model) : ChosenHead registry last root key model := by
  obtain ⟨⟨children,only⟩,plan,frame,ready,head⟩ := chosen
  obtain ⟨other,otherFrame,pair⟩ := frame_counterpart same.core (reorders_refl registry) roleEq frame
  exact ⟨⟨children,(unique same.core.current.context registry root key children).mp only⟩,other,otherFrame,
    (same.core.snapshot.ready root other).mp ((pair.ready first.core root).mp ready),(pair.head model).mp head⟩

theorem chosen_head (same : Related relation first last) (registry : Registry) (roleEq : registry.roles = roles) (root key model) :
    ChosenHead registry first root key model ↔ ChosenHead registry last root key model :=
  ⟨chosen_head_forward same registry roleEq,chosen_head_forward same.symm registry roleEq⟩

theorem chosen_effects_forward (same : Related relation first last) (registry : Registry) (roleEq : registry.roles = roles)
    (chosen : ChosenEffects registry first root key model) : ChosenEffects registry last root key model := by
  obtain ⟨⟨children,only⟩,plan,frame,ready,head,effects⟩ := chosen
  obtain ⟨other,otherFrame,pair⟩ := frame_counterpart same.core (reorders_refl registry) roleEq frame
  exact ⟨⟨children,(unique same.core.current.context registry root key children).mp only⟩,other,otherFrame,
    (same.core.snapshot.ready root other).mp ((pair.ready first.core root).mp ready),(pair.head model).mp head,
    (same.core.snapshot.effects root other model).mp ((pair.effects first.core root model).mp effects)⟩

theorem chosen_effects (same : Related relation first last) (registry : Registry) (roleEq : registry.roles = roles) (root key model) :
    ChosenEffects registry first root key model ↔ ChosenEffects registry last root key model :=
  ⟨chosen_effects_forward same registry roleEq,chosen_effects_forward same.symm registry roleEq⟩

theorem conflict (same : Related relation first last) (registry : Registry) (roleEq : registry.roles = roles) (root key) :
    OutputConflict registry first root key ↔ OutputConflict registry last root key := by
  simp only [OutputConflict,same.models,chosen_head same registry roleEq,chosen_effects same registry roleEq]

theorem administrative_ready (same : Related relation first last) (root) :
    AdministrativeReady first root ↔ AdministrativeReady last root := by
  have models := funext (fun model => propext (same.models model))
  simp only [AdministrativeReady,same.core.centers,same.core.snapshot.alias,models]

theorem pending (same : Related relation first last) (registry) (root) :
    (diagnosticBoundary roles).InspectionPending registry first root ↔
      (diagnosticBoundary roles).InspectionPending registry last root :=
  or_congr (inspection_pending same.core.current.context registry root) (not_congr (administrative_ready same root))

theorem root_pending (same : Related relation first last) (registry) (root) :
    (diagnosticBoundary roles).RootPending registry first root ↔ (diagnosticBoundary roles).RootPending registry last root :=
  GeneralNominalMetadataEquivalence.pending same.core.current.context.state (GeneralNominalCenteredHeadCandidates.inputs root).demand

theorem root_cycle (same : Related relation first last) (registry) (root) :
    (diagnosticBoundary roles).RootK2 registry first root ↔ (diagnosticBoundary roles).RootK2 registry last root := by
  apply or_congr _ (by simp only [GeneralNominalCenteredHeadMatStepCycles.RootCycle,cyclic same,same.core.centers])
  obtain ⟨allocated,reserved,equal,keys,names⟩ := same.core.current.context.replace_form
  rw [equal]
  exact (GeneralNominalCenteredPermutationCycles.root _ allocated reserved ⟨allocated,reserved,rfl,keys,names⟩ _).symm

theorem candidate_forward (same : Related relation first last) (registry : Registry) (roleEq : registry.roles = roles)
    (cycle : GeneralNominalCenteredHeadMatStepCycles.CandidateCycle registry first root) :
    GeneralNominalCenteredHeadMatStepCycles.CandidateCycle registry last root := by
  obtain ⟨plan,frame,entry,member,cycle⟩ := cycle
  obtain ⟨other,next,pair⟩ := frame_counterpart same.core (reorders_refl registry) roleEq frame
  exact ⟨other,pair.matched.packet.identity ▸ next,entry,pair.matched.tests ▸ member,(cyclic same _).mp cycle⟩

theorem candidate_cycle (same : Related relation first last) (registry : Registry) (roleEq : registry.roles = roles) (root) :
    (diagnosticBoundary roles).CandidateK2 registry first root ↔ (diagnosticBoundary roles).CandidateK2 registry last root := by
  apply or_congr _ ⟨candidate_forward same registry roleEq,candidate_forward same.symm registry roleEq⟩
  obtain ⟨allocated,reserved,equal,keys,names⟩ := same.core.current.context.replace_form
  rw [equal]
  exact (GeneralNominalCenteredPermutationCycles.candidate allocated reserved _ ⟨allocated,reserved,rfl,keys,names⟩ registry _).symm

theorem safe (same : Related relation first last) (registry : Registry) (roleEq : registry.roles = roles) (root) :
    B4TargetV6.SafeKnown (diagnosticBoundary roles) registry first root ↔
      B4TargetV6.SafeKnown (diagnosticBoundary roles) registry last root :=
  and_congr (not_congr (root_pending same registry root)) (and_congr (not_congr (root_cycle same registry root))
    (and_congr (not_congr (candidate_cycle same registry roleEq root)) (not_congr (pending same registry root))))

theorem rejection (same : Related relation first last) (registry : Registry) (roleEq : registry.roles = roles) (root) :
    B4TargetV6.RejectReason (diagnosticBoundary roles) registry first root ↔
      B4TargetV6.RejectReason (diagnosticBoundary roles) registry last root := by
  unfold B4TargetV6.RejectReason
  apply and_congr (not_congr (root_pending same registry root))
  apply or_congr (root_cycle same registry root)
  apply or_congr (candidate_cycle same registry roleEq root)
  apply and_congr (not_congr (pending same registry root))
  change ((∀ key children, ¬ GeneralNominalCenteredHeadCandidates.Survivor registry first.core.erased.current.context root key children) ∨
    ∃ key children, GeneralNominalCenteredHeadCandidates.Unique registry first.core.erased.current.context root key children ∧
      OutputConflict registry first root key) ↔ _
  simp only [survivor same.core.current.context,unique same.core.current.context,conflict same registry roleEq]
  rfl

theorem local_forward (same : Related relation first last) (registry : Registry) (roleEq : registry.roles = roles)
    (root frontier) (valid : Local registry first root frontier) : Local registry last root frontier := by
  cases valid with
  | pending given => exact .pending ((root_pending same registry root).mp given)
  | inspectionPending known given noRoot noCandidate =>
      exact .inspectionPending ((not_congr (root_pending same registry root)).mp known)
        ((pending same registry root).mp given) ((not_congr (root_cycle same registry root)).mp noRoot)
        ((not_congr (candidate_cycle same registry roleEq root)).mp noCandidate)
  | rejected reason => exact .rejected ((rejection same registry roleEq root).mp reason)
  | ambiguous ready one two different =>
      exact .ambiguous ((safe same registry roleEq root).mp ready)
        ((survivor same.core.current.context registry root _ _).mp one)
        ((survivor same.core.current.context registry root _ _).mp two) different
  | selected ready only clear =>
      exact .selected ((safe same registry roleEq root).mp ready)
        ((unique same.core.current.context registry root _ _).mp only)
        ((not_congr (conflict same registry roleEq root _)).mp clear)

theorem local_iff (same : Related relation first last) (registry : Registry) (roleEq : registry.roles = roles)
    (root frontier) : Local registry first root frontier ↔ Local registry last root frontier :=
  ⟨local_forward same registry roleEq root frontier,local_forward same.symm registry roleEq root frontier⟩

end Yulang.GeneralNominalCenteredHeadMatPermutationLocal
