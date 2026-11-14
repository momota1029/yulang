import Yulang.GeneralNominalCenteredHeadStepTableExtension
import Yulang.GeneralNominalCenteredHeadStepAvailability

set_option backward.isDefEq.respectTransparency false

/-! Installation transports the complete live-effect model extension. The
head Frame suffices for packet-table growth; no legacy Joint guard is needed. -/
namespace Yulang.GeneralNominalCenteredHeadStepInstallationPermutation
open GeneralDeclarations GeneralSourceDictionaries GeneralRegistryReordering GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects GeneralNominalCenteredHeadStepKernel
open GeneralNominalCenteredHeadStepBoundary (Local)
open GeneralNominalCenteredHeadOutputs (Frame EffectsReady OutputEquations)
open GeneralNominalCenteredPermutationCounterparts (Match counterpart)
open GeneralNominalCenteredPermutationRepresentation (RebasedPacket)
open GeneralNominalLedgerPermutation (All₂)
variable {roles : Roles.RoleDecls} {r s : Registry}
variable {left right : State roles} {plan other : Plan roles}

def Corresponds (r s : Registry) (left right : State roles) : Prop :=
  GeneralNominalCenteredPermutationRepresentation.Corresponds r s left.core right.core ∧
    All₂ GeneralNominalCenteredHeadStepEffectPermutation.EffectPair left.effects right.effects

theorem frame_counterpart
    (same : GeneralNominalCenteredLedgerPermutation.Related relation left.core right.core)
    (order : Reorders r s) (roleEq : r.roles = roles)
    (frame : Frame r left.core plan.packet.site.occurrence plan.packet.declaration.id plan) :
    ∃ other, Frame s right.core other.packet.site.occurrence other.packet.declaration.id other ∧
      Match plan other ∧ RebasedPacket r s plan.packet other.packet := by
  obtain ⟨other,reg,ctx,visible,matched,rebased⟩ := counterpart plan (frame.registry_eq ▸ order)
    (frame.registry_eq ▸ roleEq) same.erased.current.context frame.context_eq (frame.registry_eq ▸ frame.visible)
  have prepared : GeneralNominalCenteredHeadCandidates.Prepared s right.core.erased.current.context
      other.packet.site.occurrence other.packet.declaration := by
    have old : GeneralNominalCenteredHeadCandidates.Prepared plan.packet.registry plan.packet.context
        plan.packet.site.occurrence plan.packet.declaration := by
      simpa only [frame.registry_eq,frame.context_eq] using frame.prepared
    simpa only [GeneralNominalCenteredHeadCandidates.prepared_headReady,reg,ctx,matched.packet.site]
      using (matched.ready (GeneralNominalCenteredHeadCandidates.inputs plan.packet.site.occurrence)).mp old
  refine ⟨other,⟨reg,ctx,rfl,rfl,?_,?_,visible,?_,matched.located.mp frame.located,prepared⟩,
    matched,frame.registry_eq ▸ rebased⟩
  · rw [← matched.packet.site,← same.erased.current.sites]; exact frame.raw_recorded
  · rw [← matched.input]; exact (same.sites _).mp frame.center_recorded
  · rw [← matched.packet.site,← matched.declaration.role]; exact frame.role_eq

theorem counterpart_enabled (same : Corresponds r s left right) (order : Reorders r s) (roleEq : r.roles = roles)
    (recordedLeft : GeneralNominalCenteredCommitment.RecordedCommitted left.core)
    (recordedRight : GeneralNominalCenteredCommitment.RecordedCommitted right.core)
    (enabled : Installable r left plan support)
    (novel : ¬ GeneralNominalFeedbackSteps.Committed left.core.erased.current plan.packet) :
    ∃ other, ∃ nextEnabled : Installable s right other support,
      ¬ GeneralNominalFeedbackSteps.Committed right.core.erased.current other.packet ∧
      Match plan other ∧ Corresponds r s (install left plan support enabled) (install right other support nextEnabled) := by
  obtain ⟨table,rebases,recorded,ledger⟩ := same.1
  have paired : GeneralNominalCenteredHeadStepEffectPermutation.Related
      (GeneralNominalCenteredPermutationRepresentation.paired table) left right := ⟨ledger,same.2⟩
  obtain ⟨other,frame,matched,rebased⟩ := frame_counterpart ledger order roleEq enabled.frame
  have pair := GeneralNominalCenteredHeadStepEffectPermutation.plan_pair rebased matched.input
  have novelOther : ¬ GeneralNominalFeedbackSteps.Committed right.core.erased.current other.packet :=
    fun committed => novel ((ledger.erased.current.committed matched.packet.toPacketPair).mpr committed)
  have oneNew : plan.packet ∉ left.core.erased.current.packets := fun member => novel (recordedLeft _ member)
  have twoNew : other.packet ∉ right.core.erased.current.packets := fun member => novelOther (recordedRight _ member)
  have installedCore := GeneralNominalCenteredHeadStepTableExtension.installed_corresponds same.1 order roleEq matched rebased
    oneNew twoNew enabled.frame frame support
  obtain ⟨nextTable,nextRebases,nextRecorded,nextCore⟩ := installedCore
  have requests := GeneralNominalCenteredHeadStepEffectPermutation.requests_eq ledger.erased.current
  have nextRequests := GeneralNominalCenteredHeadStepEffectPermutation.requests_eq nextCore.erased.current
  have selection : Local s right other.packet.site.occurrence (.selected other.packet.declaration.id other.packet.children) := by
    have old := GeneralNominalCenteredHeadStepBoundary.installable_selected enabled
    have moved := (GeneralNominalCenteredHeadStepObservationPermutation.local_iff paired r roleEq _ _).mp old
    have reordered := (GeneralNominalCenteredHeadStepOrder.local_iff order right _ _).mp moved
    simpa only [matched.packet.site,matched.packet.identity,matched.packet.children] using reordered
  have newReady : EffectsReady right.core other.packet.site.occurrence other := by
    have moved := (pair.ready left.core plan.packet.site.occurrence).mp enabled.ready
    rw [pair.root] at moved
    exact (GeneralNominalCenteredHeadStepEffectPermutation.requests_ready (requests _) other).mp moved
  have materialized : (GeneralNominalRecursiveCandidates.generated other.packet.registry other.packet.context
      other.packet.site.occurrence other.packet.declaration other.packet.checked other.packet.bounds).unknown = false := by
    change (GeneralNominalPacketSupport.namedSchema other.packet).unknown = false
    rw [← matched.packet.named]
    exact enabled.materialized
  have packetOrder : Reorders plan.packet.registry other.packet.registry := by
    simpa only [enabled.frame.registry_eq,frame.registry_eq] using order
  have values : GeneralNominalValueSupport.PacketGuard right.core.erased other.packet support :=
    ⟨(GeneralNominalCenteredPermutationGuards.choices ledger.erased packetOrder matched enabled.frame.context_eq frame.context_eq
      (enabled.frame.registry_eq ▸ enabled.frame.visible) (frame.registry_eq ▸ frame.visible)
      enabled.frame.role_eq frame.role_eq enabled.frame.located frame.located support).mp enabled.valueSupport.1,
      (ledger.erased.supported packetOrder support).mp enabled.valueSupport.2⟩
  have common : ∃ model, InstallationModels right other support model := by
    obtain ⟨model,valid,branch,outputs,successor,live⟩ := enabled.common
    refine ⟨model,(paired.models model).mp valid,
      ⟨(matched.packet.holds model).mp branch.1,(matched.plans.equations model).mp branch.2⟩,?_,?_,?_⟩
    · have moved := (pair.output left.core plan.packet.site.occurrence model).mp outputs
      rw [pair.root] at moved
      exact (GeneralNominalCenteredHeadStepEffectPermutation.requests_output (requests _) other model).mp moved
    · have moved := (pair.output (GeneralNominalCenteredSteps.install left.core plan support) plan.packet.site.occurrence model).mp successor
      rw [pair.root] at moved
      exact (GeneralNominalCenteredHeadStepEffectPermutation.requests_output (nextRequests _) other model).mp moved
    · intro effect member
      obtain ⟨old,present,effectPair⟩ := GeneralNominalLedgerPermutation.all₂_right same.2 member
      exact (effectPair.live nextRequests model).mp (live old present)
  have nextEnabled : Installable s right other support := by
    have positions := GeneralNominalCenteredHeadStepAvailability.selected_safe selection other frame.center_recorded
      other.input_exact frame.registry_eq frame.context_eq frame.visible frame.role_eq
      (frame.context_eq ▸ frame.prepared) frame.located
    have alternatives := GeneralNominalCenteredHeadStepAvailability.selected_alternatives selection other.input frame.center_recorded other.input_exact
    cases selection with
    | selected safe unique clear =>
        exact ⟨frame,unique,safe,newReady,materialized,
          (GeneralNominalCenteredPermutationInstallable.choice ledger.erased.current matched.packet.toPacketPair).mp enabled.choice,
          values,positions,alternatives,common⟩
  refine ⟨other,nextEnabled,novelOther,matched,⟨nextTable,nextRebases,nextRecorded,nextCore⟩,?_⟩
  refine .cons ⟨pair,?_⟩ same.2
  change GeneralNominalCenteredHeadOutputs.requests left.core plan.packet.site.occurrence =
    GeneralNominalCenteredHeadOutputs.requests right.core other.packet.site.occurrence
  rw [pair.root]
  exact requests _

end Yulang.GeneralNominalCenteredHeadStepInstallationPermutation
