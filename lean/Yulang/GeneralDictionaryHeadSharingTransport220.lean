import Yulang.GeneralDictionaryHeadSharingBoundary220
import Yulang.GeneralDictionaryDefaultCanonical208

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryHeadSharingTransport220
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters GeneralRegistryReordering
open GeneralNominalCenteredHeadMatStepJournal (State Models)
open GeneralNominalCenteredHeadOutputs (Frame)
open GeneralNominalCenteredHeadMatPermutationRaw (Core)
open GeneralNominalCenteredHeadMatPermutationLedger (Related)
open GeneralDictionaryHeadSharingConflict220
open GeneralDictionaryHeadSharingBoundary220 (boundary Local)
variable {roles : Roles.RoleDecls} {first last : State roles}

theorem frames (same : Core first.core last.core) (order : Reorders registry other)
    (roleEq : registry.roles = roles) :
    (∃ plan, Frame registry first.core root key plan) ↔ ∃ plan, Frame other last.core root key plan := by
  constructor
  · rintro ⟨plan,frame⟩
    obtain ⟨next,framed,_⟩ := GeneralNominalCenteredHeadMatPermutationLocal.frame_counterpart same order roleEq frame
    exact ⟨next,framed⟩
  · rintro ⟨plan,frame⟩
    obtain ⟨next,framed,_⟩ := GeneralNominalCenteredHeadMatPermutationLocal.frame_counterpart same.symm
      (GeneralRegistryChildOrder.reorders_symm order) (order.2.1.symm.trans roleEq) frame
    exact ⟨next,framed⟩

theorem feasible_forward (same : Core first.core last.core) (order : Reorders registry other)
    (roleEq : registry.roles = roles) (models : ∀ model, Models first model ↔ Models last model)
    (given : Feasible registry first root key) : Feasible other last root key := by
  obtain ⟨model,valid,plan,frame,holds⟩ := given
  obtain ⟨next,framed,pair⟩ := GeneralNominalCenteredHeadMatPermutationLocal.frame_counterpart same order roleEq frame
  exact ⟨model,(models model).mp valid,next,framed,(GeneralDictionaryHeadSharing220.holds_pair pair model).mp holds⟩

theorem feasible (same : Core first.core last.core) (order : Reorders registry other)
    (roleEq : registry.roles = roles) (models : ∀ model, Models first model ↔ Models last model) :
    Feasible registry first root key ↔ Feasible other last root key :=
  ⟨feasible_forward same order roleEq models,
    feasible_forward same.symm (GeneralRegistryChildOrder.reorders_symm order)
      (order.2.1.symm.trans roleEq) (fun model => (models model).symm)⟩

theorem atKey (same : Core first.core last.core) (order : Reorders registry other)
    (roleEq : registry.roles = roles) (models : ∀ model, Models first model ↔ Models last model) :
    AtKey registry first root key ↔ AtKey other last root key := by
  simp only [AtKey,models,frames same order roleEq,feasible same order roleEq models]

theorem conflict_order (order : Reorders value other) (roleEq : value.roles = roles) (state : State roles) :
    Conflict value state root ↔ Conflict other state root := by
  unfold Conflict
  have compiled := GeneralNominalCenteredHeadAllocEncoding.registry_reorders order
  have atKeyEq (key : Nat) := atKey (Core.refl state.core) compiled roleEq (fun _ => Iff.rfl) (root := root) (key := key)
  have uniqueEq := GeneralNominalCenteredHeadStepOrder.unique compiled state.core.erased.current.context root
  change (∃ key children, GeneralNominalCenteredHeadCandidates.Unique _ _ _ key children ∧ _) ↔
    (∃ key children, GeneralNominalCenteredHeadCandidates.Unique _ _ _ key children ∧ _)
  have safeEq : B4TargetV7.SafeKnown (GeneralDictionaryDefaultBoundary208.boundary roles) value state root ↔
      B4TargetV7.SafeKnown (GeneralDictionaryDefaultBoundary208.boundary roles) other state root :=
    GeneralNominalCenteredHeadMatStepOrder.safe compiled state root
  simp only [uniqueEq,atKeyEq,safeEq]

theorem conflict_related (same : Related relation first last) (value : Registry) (roleEq : value.roles = roles) :
    Conflict value first root ↔ Conflict value last root := by
  unfold Conflict
  have atKeyEq (key : Nat) := atKey same.core (reorders_refl (GeneralNominalCenteredHeadAllocEncoding.registry value))
    roleEq same.models (root := root) (key := key)
  have uniqueEq := GeneralNominalCenteredHeadStepObservationPermutation.unique same.core.current.context
    (GeneralNominalCenteredHeadAllocEncoding.registry value) root
  change (∃ key children, GeneralNominalCenteredHeadCandidates.Unique _ _ _ key children ∧ _) ↔
    (∃ key children, GeneralNominalCenteredHeadCandidates.Unique _ _ _ key children ∧ _)
  have safeEq : B4TargetV7.SafeKnown (GeneralDictionaryDefaultBoundary208.boundary roles) value first root ↔
      B4TargetV7.SafeKnown (GeneralDictionaryDefaultBoundary208.boundary roles) value last root :=
    GeneralNominalCenteredHeadMatPermutationLocal.safe same
      (GeneralNominalCenteredHeadAllocEncoding.registry value) roleEq root
  simp only [uniqueEq,atKeyEq,safeEq]

theorem local_order (order : Reorders value other) (roleEq : value.roles = roles)
    (state : State roles) (focus frontier) : Local value state focus frontier ↔ Local other state focus frontier := by
  refine B4TargetV8.local_transport (b := boundary roles) (other := boundary roles) ?_ ?_ ?_ frontier
  · exact fun _ => GeneralDictionaryDefaultCanonical208.local_order order state focus _
  · exact conflict_order order roleEq state
  · exact GeneralNominalCenteredHeadAllocV7Boundary.priority_order
      (GeneralNominalCenteredHeadAllocEncoding.registry_reorders order) state focus

theorem local_related (same : Related relation first last) (value : Registry) (roleEq : value.roles = roles)
    (focus frontier) : Local value first focus frontier ↔ Local value last focus frontier := by
  refine B4TargetV8.local_transport (b := boundary roles) (other := boundary roles) ?_ ?_ ?_ frontier
  · exact fun _ => GeneralDictionaryDefaultCanonical208.local_related same value roleEq focus _
  · exact conflict_related same value roleEq
  · exact GeneralNominalCenteredHeadAllocV7Boundary.priority_related same
      (GeneralNominalCenteredHeadAllocEncoding.registry value) roleEq focus

end Yulang.GeneralDictionaryHeadSharingTransport220
