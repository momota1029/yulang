import Yulang.GeneralNominalCenteredHeadStepEffectPermutation

set_option backward.isDefEq.respectTransparency false

/-! Head observations and class effects transport across paired current
contexts. The same model assignment interprets each historical ledger pair. -/
namespace Yulang.GeneralNominalCenteredHeadStepObservationPermutation
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralRegistryReordering GeneralNominalCenteredHeadCandidates GeneralNominalCenteredHeadOutputs
open GeneralNominalCenteredHeadStepEffects (State Models)
open GeneralNominalCenteredHeadStepEffectPermutation (Related PlanPair requests_eq)
open GeneralNominalCenteredPermutationCounterparts (Match counterpart)
open GeneralNominalCenteredPermutationContext (context)
variable {roles : Roles.RoleDecls}

theorem prepared (same : GeneralNominalJournalPermutation.ContextPair one two) (registry) (root : Occurrence roles) (declaration) :
    Prepared registry one root declaration ↔ Prepared registry two root declaration :=
  GeneralNominalCenteredPermutationApplicability.head_ready same registry (inputs root) declaration

theorem failed (same : GeneralNominalJournalPermutation.ContextPair one two) (registry) (root : Occurrence roles) (declaration) :
    Failed registry one root declaration ↔ Failed registry two root declaration := by
  obtain ⟨allocated,reserved,rfl,keys,names⟩ := same.replace_form
  have metadata : GeneralNominalMetadataEquivalence.Same one.state
      (GeneralNominalMetadataEquivalence.replace one.state allocated reserved) := ⟨allocated,reserved,rfl,keys,names⟩
  change Failed registry one root declaration ↔ Failed registry (context one allocated reserved) root declaration
  simp only [Failed,HeadModels,GeneralNominalCenteredPermutationContext.private_models one allocated reserved,
    GeneralNominalCenteredPermutationContext.report one allocated reserved,
    GeneralNominalMetadataEquivalence.fresh metadata]
  simp only [context,GeneralNominalReportMetadata.projectionModels]
  rfl

theorem survivor (same : GeneralNominalJournalPermutation.ContextPair one two) (registry) (root : Occurrence roles) (key children) :
    Survivor registry one root key children ↔ Survivor registry two root key children := by
  have ready := prepared (roles := roles) same registry root
  obtain ⟨allocated,reserved,rfl,keys,names⟩ := same.replace_form
  change Survivor registry one root key children ↔ Survivor registry (context one allocated reserved) root key children
  simp only [Survivor,ready,GeneralNominalCenteredPermutationContext.children one allocated reserved]
  rfl

theorem unique (same : GeneralNominalJournalPermutation.ContextPair one two) (registry) (root : Occurrence roles) (key children) :
    Unique registry one root key children ↔ Unique registry two root key children := by
  simp only [Unique,survivor same registry root]

theorem inspection_pending (same : GeneralNominalJournalPermutation.ContextPair one two) (registry) (root : Occurrence roles) :
    InspectionPending registry one root ↔ InspectionPending registry two root := by
  simp only [InspectionPending,failed same registry root,prepared same registry root,
    GeneralNominalMetadataEquivalence.pending same.state]

variable {relation : GeneralNominalSaturationState.Packet roles → GeneralNominalSaturationState.Packet roles → Prop}
variable {left right : GeneralNominalCenteredSteps.State roles}

theorem frame_counterpart (same : GeneralNominalCenteredLedgerPermutation.Related relation left right)
    (registry : Registry) (roleEq : registry.roles = roles)
    (frame : Frame registry left root key plan) :
    ∃ other, Frame registry right root key other ∧ PlanPair plan other := by
  have order : Reorders plan.packet.registry registry := frame.registry_eq ▸ reorders_refl registry
  obtain ⟨other,reg,ctx,visible,matched,rebased⟩ := counterpart plan order (frame.registry_eq ▸ roleEq)
    same.erased.current.context frame.context_eq (frame.registry_eq ▸ frame.visible)
  have packetRoot : other.packet.site.occurrence = root :=
    (congrArg GeneralNominalDemandMerging.Site.occurrence matched.packet.site).symm.trans frame.occurrence_eq
  have ready : Prepared registry right.erased.current.context root other.packet.declaration := by
    have old : Prepared plan.packet.registry plan.packet.context root plan.packet.declaration := by
      simpa only [frame.registry_eq,frame.context_eq] using frame.prepared
    simpa only [prepared_headReady,reg,ctx] using (matched.ready (inputs root)).mp old
  have located : GeneralNominalRecursiveCandidates.arguments other.packet.context (inputs root) = some other.packet.bounds := by
    have old : GeneralNominalRecursiveCandidates.arguments plan.packet.context plan.packet.site.occurrence = some plan.packet.bounds :=
      frame.occurrence_eq ▸ frame.located
    change GeneralNominalRecursiveCandidates.arguments other.packet.context root = some other.packet.bounds
    simpa only [packetRoot] using matched.located.mp old
  refine ⟨other,⟨reg,ctx,packetRoot,matched.packet.identity.symm.trans frame.key_eq,?_,?_,visible,
    matched.declaration.role.symm.trans frame.role_eq,located,ready⟩,
    GeneralNominalCenteredHeadStepEffectPermutation.plan_pair rebased matched.input⟩
  · rw [← matched.packet.site,← same.erased.current.sites]; exact frame.raw_recorded
  · rw [← matched.input]; exact (same.sites _).mp frame.center_recorded

theorem chosen_head_forward (same : GeneralNominalCenteredLedgerPermutation.Related relation left right)
    (registry : Registry) (roleEq : registry.roles = roles) (root : Occurrence roles) (key model)
    (chosen : ChosenHead registry left root key model) : ChosenHead registry right root key model := by
  obtain ⟨⟨children,only⟩,plan,frame,ready,head⟩ := chosen
  obtain ⟨other,otherFrame,pair⟩ := frame_counterpart same registry roleEq frame
  refine ⟨⟨children,(unique same.erased.current.context registry root key children).mp only⟩,other,otherFrame,?_,(pair.head model).mp head⟩
  exact (GeneralNominalCenteredHeadStepEffectPermutation.requests_ready (requests_eq same.erased.current root) other).mp
    ((pair.ready left root).mp ready)

theorem chosen_head (same : GeneralNominalCenteredLedgerPermutation.Related relation left right)
    (registry : Registry) (roleEq : registry.roles = roles) (root : Occurrence roles) (key model) :
    ChosenHead registry left root key model ↔ ChosenHead registry right root key model :=
  ⟨chosen_head_forward same registry roleEq root key model,
    chosen_head_forward (GeneralNominalCenteredPermutationSafety.symm same) registry roleEq root key model⟩

theorem chosen_effects_forward (same : GeneralNominalCenteredLedgerPermutation.Related relation left right)
    (registry : Registry) (roleEq : registry.roles = roles) (root : Occurrence roles) (key model)
    (chosen : ChosenClassEffects registry left root key model) : ChosenClassEffects registry right root key model := by
  obtain ⟨⟨children,only⟩,plan,frame,ready,head,outputs⟩ := chosen
  obtain ⟨other,otherFrame,pair⟩ := frame_counterpart same registry roleEq frame
  refine ⟨⟨children,(unique same.erased.current.context registry root key children).mp only⟩,other,otherFrame,?_,(pair.head model).mp head,?_⟩
  · exact (GeneralNominalCenteredHeadStepEffectPermutation.requests_ready (requests_eq same.erased.current root) other).mp
      ((pair.ready left root).mp ready)
  · exact (GeneralNominalCenteredHeadStepEffectPermutation.requests_output (requests_eq same.erased.current root) other model).mp
      ((pair.output left root model).mp outputs)

theorem chosen_effects (same : GeneralNominalCenteredLedgerPermutation.Related relation left right)
    (registry : Registry) (roleEq : registry.roles = roles) (root : Occurrence roles) (key model) :
    ChosenClassEffects registry left root key model ↔ ChosenClassEffects registry right root key model :=
  ⟨chosen_effects_forward same registry roleEq root key model,
    chosen_effects_forward (GeneralNominalCenteredPermutationSafety.symm same) registry roleEq root key model⟩

theorem candidate_forward (same : GeneralNominalCenteredLedgerPermutation.Related relation left right)
    (registry : Registry) (roleEq : registry.roles = roles) (root : Occurrence roles)
    (cycle : GeneralNominalCenteredHeadBoundary.CandidateCycle registry left root) :
    GeneralNominalCenteredHeadBoundary.CandidateCycle registry right root := by
  obtain ⟨plan,recorded,input,registryEq,contextEq,visible,role,ready,located,entry,member,cyclic⟩ := cycle
  have order : Reorders plan.packet.registry registry := registryEq ▸ reorders_refl registry
  obtain ⟨other,reg,ctx,present,matched,_⟩ := counterpart plan order (registryEq ▸ roleEq)
    same.erased.current.context contextEq (registryEq ▸ visible)
  have inputOther : other.input.occurrence = root := (congrArg Site.occurrence matched.input).symm.trans input
  have rootEq : plan.packet.site.occurrence = root := plan.input_exact.symm.trans input
  have rootOther : other.packet.site.occurrence = root :=
    (congrArg GeneralNominalDemandMerging.Site.occurrence matched.packet.site).symm.trans rootEq
  have readyOther : Prepared registry other.packet.context root other.packet.declaration := by
    have old : Prepared plan.packet.registry plan.packet.context root plan.packet.declaration := registryEq ▸ ready
    simpa only [prepared_headReady,reg] using (matched.ready (inputs root)).mp old
  have locatedOther : GeneralNominalRecursiveCandidates.arguments other.packet.context (inputs root) = some other.packet.bounds := by
    have old : GeneralNominalRecursiveCandidates.arguments plan.packet.context plan.packet.site.occurrence = some plan.packet.bounds := rootEq ▸ located
    change GeneralNominalRecursiveCandidates.arguments other.packet.context root = some other.packet.bounds
    simpa only [rootOther] using matched.located.mp old
  exact ⟨other,(matched.input ▸ (same.sites _).mp recorded),inputOther,reg,ctx,present,
    matched.declaration.role.symm.trans role,readyOther,locatedOther,entry,matched.tests ▸ member,
    (GeneralNominalCenteredPermutationSafety.cyclic same _).mp cyclic⟩

theorem candidate (same : GeneralNominalCenteredLedgerPermutation.Related relation left right)
    (registry : Registry) (roleEq : registry.roles = roles) (root : Occurrence roles) :
    GeneralNominalCenteredHeadBoundary.CandidateCycle registry left root ↔
      GeneralNominalCenteredHeadBoundary.CandidateCycle registry right root :=
  ⟨candidate_forward same registry roleEq root,
    candidate_forward (GeneralNominalCenteredPermutationSafety.symm same) registry roleEq root⟩

theorem deferred_cycles (same : GeneralNominalJournalPermutation.ContextPair one two) (registry) (root : Occurrence roles) :
    ((GeneralNominalMixedRecurrence.RootK2 one.state (inputs root).demand ∧
      ¬ GeneralNominalCycleK2.RootK2 one.state (inputs root).demand) ∨
      (GeneralNominalRecursiveCandidates.CandidateK2 registry one (inputs root) ∧
        ¬ GeneralNominalCycleK2.CandidateK2 registry one (inputs root))) ↔
    ((GeneralNominalMixedRecurrence.RootK2 two.state (inputs root).demand ∧
      ¬ GeneralNominalCycleK2.RootK2 two.state (inputs root).demand) ∨
      (GeneralNominalRecursiveCandidates.CandidateK2 registry two (inputs root) ∧
        ¬ GeneralNominalCycleK2.CandidateK2 registry two (inputs root))) := by
  obtain ⟨allocated,reserved,rfl,keys,names⟩ := same.replace_form
  have metadata : GeneralNominalMetadataEquivalence.Same one.state
      (GeneralNominalMetadataEquivalence.replace one.state allocated reserved) := ⟨allocated,reserved,rfl,keys,names⟩
  exact or_congr
    (and_congr (GeneralNominalCenteredPermutationCycles.mixed_root one.state allocated reserved metadata _).symm
      (not_congr (GeneralNominalCenteredPermutationCycles.root one.state allocated reserved metadata _).symm))
    (and_congr (GeneralNominalCenteredPermutationCycles.recursive_candidate allocated reserved one metadata registry _).symm
      (not_congr (GeneralNominalCenteredPermutationCycles.candidate allocated reserved one metadata registry _).symm))

theorem pending (same : GeneralNominalCenteredLedgerPermutation.Related relation left right)
    (registry) (root : Occurrence roles) :
    GeneralNominalCenteredHeadBoundary.InspectionPending registry left root ↔
      GeneralNominalCenteredHeadBoundary.InspectionPending registry right root := by
  exact or_congr (inspection_pending same.erased.current.context registry root)
    (or_congr (and_congr (not_congr (GeneralNominalMetadataEquivalence.pending same.erased.current.context.state _))
      (deferred_cycles same.erased.current.context registry root))
      (or_congr (not_congr (GeneralNominalCenteredPermutationGuards.centered_decision same (reorders_refl registry) root))
        (not_congr (GeneralNominalCenteredPermutationObservations.administrative_ready same root))))

variable {first last : State roles}

theorem conflict (same : Related relation first last) (registry : Registry) (roleEq : registry.roles = roles)
    (root : Occurrence roles) (key) :
    GeneralNominalCenteredHeadStepBoundary.OutputConflict registry first root key ↔
      GeneralNominalCenteredHeadStepBoundary.OutputConflict registry last root key := by
  simp only [GeneralNominalCenteredHeadStepBoundary.OutputConflict,same.models,
    chosen_head same.core registry roleEq root,chosen_effects same.core registry roleEq root]

open GeneralNominalCenteredHeadStepBoundary (boundary Local)

theorem root_pending (same : Related relation first last) (registry) (root : Occurrence roles) :
    (boundary roles).RootPending registry first root ↔ (boundary roles).RootPending registry last root :=
  GeneralNominalMetadataEquivalence.pending same.core.erased.current.context.state (inputs root).demand

theorem root_cycle (same : Related relation first last) (registry) (root : Occurrence roles) :
    (boundary roles).RootK2 registry first root ↔ (boundary roles).RootK2 registry last root :=
  or_congr (GeneralNominalCenteredPermutationApplicability.feedback_root same.core.erased.current (inputs root))
    (GeneralNominalCenteredPermutationSafety.root_cycle same.core root)

theorem candidate_cycle (same : Related relation first last) (registry : Registry) (roleEq : registry.roles = roles)
    (root : Occurrence roles) :
    (boundary roles).CandidateK2 registry first root ↔ (boundary roles).CandidateK2 registry last root :=
  or_congr (GeneralNominalCenteredPermutationApplicability.feedback_candidate same.core.erased.current registry (inputs root))
    (candidate same.core registry roleEq root)

theorem safe (same : Related relation first last) (registry : Registry) (roleEq : registry.roles = roles) (root : Occurrence roles) :
    B4TargetV6.SafeKnown (boundary roles) registry first root ↔ B4TargetV6.SafeKnown (boundary roles) registry last root :=
  and_congr (not_congr (root_pending same registry root)) (and_congr (not_congr (root_cycle same registry root))
    (and_congr (not_congr (candidate_cycle same registry roleEq root)) (not_congr (pending same.core registry root))))

theorem rejection (same : Related relation first last) (registry : Registry) (roleEq : registry.roles = roles) (root : Occurrence roles) :
    B4TargetV6.RejectReason (boundary roles) registry first root ↔ B4TargetV6.RejectReason (boundary roles) registry last root := by
  unfold B4TargetV6.RejectReason
  apply and_congr (not_congr (root_pending same registry root))
  apply or_congr (root_cycle same registry root)
  apply or_congr (candidate_cycle same registry roleEq root)
  apply and_congr (not_congr (pending same.core registry root))
  change ((∀ key children, ¬ Survivor registry first.core.erased.current.context root key children) ∨
    ∃ key children, Unique registry first.core.erased.current.context root key children ∧
      GeneralNominalCenteredHeadStepBoundary.OutputConflict registry first root key) ↔ _
  simp only [survivor same.core.erased.current.context,unique same.core.erased.current.context,conflict same registry roleEq]
  rfl

theorem local_forward (same : Related relation first last) (registry : Registry) (roleEq : registry.roles = roles)
    (root : Occurrence roles) (frontier) (valid : Local registry first root frontier) : Local registry last root frontier := by
  cases valid with
  | pending given => exact .pending ((root_pending same registry root).mp given)
  | inspectionPending known given noRoot noCandidate =>
      exact .inspectionPending ((not_congr (root_pending same registry root)).mp known)
        ((pending same.core registry root).mp given) ((not_congr (root_cycle same registry root)).mp noRoot)
        ((not_congr (candidate_cycle same registry roleEq root)).mp noCandidate)
  | rejected reason => exact .rejected ((rejection same registry roleEq root).mp reason)
  | ambiguous ready one two different =>
      exact .ambiguous ((safe same registry roleEq root).mp ready)
        ((survivor same.core.erased.current.context registry root _ _).mp one)
        ((survivor same.core.erased.current.context registry root _ _).mp two) different
  | selected ready only clear =>
      exact .selected ((safe same registry roleEq root).mp ready)
        ((unique same.core.erased.current.context registry root _ _).mp only)
        ((not_congr (conflict same registry roleEq root _)).mp clear)

theorem local_iff (same : Related relation first last) (registry : Registry) (roleEq : registry.roles = roles)
    (root : Occurrence roles) (frontier) : Local registry first root frontier ↔ Local registry last root frontier :=
  ⟨local_forward same registry roleEq root frontier,local_forward same.symm registry roleEq root frontier⟩

end Yulang.GeneralNominalCenteredHeadStepObservationPermutation
