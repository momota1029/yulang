import Yulang.GeneralNominalCenteredHeadAllocMergedConflict

set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralNominalCenteredHeadAllocV7Boundary
open GeneralDeclarations GeneralSourceDictionaries CommonRoleOutermostResolver
open GeneralNominalCenteredHeadMatStepJournal (State)
open GeneralNominalCenteredHeadAllocMergedConflict (MergedOutputConflict)
open GeneralNominalCenteredHeadMatPermutationLedger (Related)
open GeneralNominalCenteredHeadAllocEncoding (registry)
variable {roles : Roles.RoleDecls}

def kernel (roles : Roles.RoleDecls) : B4TargetV7.SourceBoundary (GeneralNominalCenteredHeadMatStepLocal.vocabulary roles) where
  toV6 := GeneralNominalCenteredHeadMatStepBoundary.boundary roles
  MergedOutputConflict := fun _ => MergedOutputConflict

abbrev KernelLocal (value : Registry) (state : State roles) := B4TargetV7.Local (kernel roles) value state

def boundary (roles : Roles.RoleDecls) : B4TargetV7.SourceBoundary (GeneralNominalCenteredHeadMatStepLocal.vocabulary roles) where
  toV6 := GeneralNominalCenteredHeadAllocBoundary.boundary roles
  MergedOutputConflict := fun _ => MergedOutputConflict

abbrev Local (value : Registry) (state : State roles) := B4TargetV7.Local (boundary roles) value state
abbrev Step (value : Registry) := GeneralNominalCenteredHeadAllocBoundary.Step value (roles := roles)
abbrev Stable (value : Registry) := GeneralNominalCenteredHeadAllocBoundary.Stable value (roles := roles)

theorem local_iff {value : Registry} {state : State roles} {demand : Occurrence roles} : Local value state demand frontier ↔ KernelLocal (registry value) state demand frontier :=
  B4TargetV7.local_transport (b := boundary roles) (other := kernel roles) (r := value) (rr := registry value) (s := state) (ss := state) (d := demand) (dd := demand) (fun _ => GeneralNominalCenteredHeadAllocBoundary.local_iff) Iff.rfl Iff.rfl frontier

theorem local_eq {value : Registry} {state : State roles} : Local value state = KernelLocal (registry value) state := by
  funext demand frontier
  exact propext local_iff

theorem checked_compiled (checked : (boundary roles).Checked value) : (kernel roles).Checked (registry value) :=
  GeneralNominalCenteredHeadAllocBoundary.checked_compiled checked

theorem initial_compiled (initial : (boundary roles).Initial value root state) : (kernel roles).Initial (registry value) root state :=
  GeneralNominalCenteredHeadAllocBoundary.initial_compiled initial

theorem reachable_compiled (reachable : B4TargetV7.Reachable (boundary roles) value root state) :
    B4TargetV7.Reachable (kernel roles) (registry value) root state :=
  GeneralNominalCenteredHeadAllocBoundary.reachable_compiled reachable

theorem kernel_total (checked : Checked value) (state : State roles) (root : Occurrence roles) :
    ∃ frontier, KernelLocal value state root frontier :=
  B4TargetV7.local_total (fun _ _ _ one two => GeneralNominalCenteredHeadCandidates.survivor_children_functional checked one two)

theorem local_total (checked : (boundary roles).Checked value) (state : State roles) (root : Occurrence roles) :
    ∃ frontier, Local value state root frontier := by
  obtain ⟨frontier,chosen⟩ := kernel_total (GeneralNominalCenteredHeadAllocBoundary.checked_compiled checked).2 state root
  exact ⟨frontier,local_iff.mpr chosen⟩

theorem local_functional (one : Local value state root first) (two : Local value state root last) : first = last :=
  B4TargetV7.local_functional one two

theorem kernel_whereAccessible (value : Registry) (state : State roles) (root : Occurrence roles) :
    Acc (Child (KernelLocal value state)) root := by
  have old := GeneralNominalCenteredHeadMatStepBoundary.whereAccessible value state root
  induction old with
  | intro node prior ih => exact .intro node (fun child edge => ih child (B4TargetV7.child_prior edge))

theorem whereAccessible (value : Registry) (state : State roles) (root : Occurrence roles) :
    Acc (Child (Local value state)) root := by
  have old := GeneralNominalCenteredHeadAllocBoundary.whereAccessible value state root
  induction old with
  | intro node prior ih => exact .intro node (fun child edge => ih child (B4TargetV7.child_prior edge))

theorem priority_order (order : GeneralRegistryReordering.Reorders first last) (state : State roles) (focus : Occurrence roles) :
    B4TargetV7.PriorityAmbiguity (kernel roles) first state focus ↔ B4TargetV7.PriorityAmbiguity (kernel roles) last state focus := by
  unfold B4TargetV7.PriorityAmbiguity
  apply and_congr (not_congr (and_congr Iff.rfl (or_congr Iff.rfl (GeneralNominalCenteredHeadMatStepOrder.candidate order state focus))))
  change (∃ a xs b ys, GeneralNominalCenteredHeadCandidates.Survivor first _ focus a xs ∧
    GeneralNominalCenteredHeadCandidates.Survivor first _ focus b ys ∧ a ≠ b) ↔ _
  simp only [GeneralNominalCenteredHeadStepOrder.survivor order]
  rfl

theorem kernel_order (order : GeneralRegistryReordering.Reorders first last) (state : State roles) (focus : Occurrence roles) (frontier) :
    KernelLocal first state focus frontier ↔ KernelLocal last state focus frontier :=
  B4TargetV7.local_transport (b := kernel roles) (other := kernel roles) (r := first) (rr := last) (s := state) (ss := state) (d := focus) (dd := focus) (GeneralNominalCenteredHeadMatStepOrder.local_iff order state focus) Iff.rfl
    (priority_order order state focus) frontier

theorem priority_related {first last : State roles} {relation : GeneralNominalCenters.Plan roles → GeneralNominalCenters.Plan roles → Prop} (same : Related relation first last) (value : Registry) (roleEq : value.roles = roles) (focus : Occurrence roles) :
    B4TargetV7.PriorityAmbiguity (kernel roles) value first focus ↔ B4TargetV7.PriorityAmbiguity (kernel roles) value last focus := by
  unfold B4TargetV7.PriorityAmbiguity
  apply and_congr (not_congr (and_congr (not_congr (GeneralNominalCenteredHeadMatPermutationLocal.root_pending same value focus))
    (or_congr (GeneralNominalCenteredHeadMatPermutationLocal.root_cycle same value focus)
      (GeneralNominalCenteredHeadMatPermutationLocal.candidate_cycle same value roleEq focus))))
  change (∃ a xs b ys, GeneralNominalCenteredHeadCandidates.Survivor value _ focus a xs ∧
    GeneralNominalCenteredHeadCandidates.Survivor value _ focus b ys ∧ a ≠ b) ↔ _
  simp only [GeneralNominalCenteredHeadStepObservationPermutation.survivor same.core.current.context]
  rfl

theorem kernel_related {first last : State roles} {relation : GeneralNominalCenters.Plan roles → GeneralNominalCenters.Plan roles → Prop} (same : Related relation first last) (value : Registry) (roleEq : value.roles = roles) (focus : Occurrence roles) (frontier) :
    KernelLocal value first focus frontier ↔ KernelLocal value last focus frontier :=
  B4TargetV7.local_transport
    (fun _ => GeneralNominalCenteredHeadMatStepBoundary.local_iff.trans
      ((GeneralNominalCenteredHeadMatPermutationLocal.local_iff same value roleEq _ _).trans
        GeneralNominalCenteredHeadMatStepBoundary.local_iff.symm))
    (GeneralNominalCenteredHeadAllocMergedConflict.conflict_related same focus) (priority_related same value roleEq focus) frontier

theorem stepModels (value : Registry) (checked : (boundary roles).Checked value) (root : Occurrence roles)
    (before after : State roles) (reachable : B4TargetV7.Reachable (boundary roles) value root before)
    (step : Step value root before after) : ∀ model, (boundary roles).Models after model → (boundary roles).Models before model :=
  GeneralNominalCenteredHeadAllocBoundary.stepModels value checked root before after reachable step

theorem closure (value : Registry) (checked : (boundary roles).Checked value) (state : State roles)
    (root : Occurrence roles) (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (halted : ∀ next, ¬ Step value root state next) :
    Stable value state root ∧ ∀ child, (boundary roles).Generated value state root child → Stable value state child :=
  GeneralNominalCenteredHeadAllocBoundary.closure value checked state root reachable halted

theorem initialReorders (order : (boundary roles).Reorders first last)
    (initial : (boundary roles).Initial first root state) : (boundary roles).Initial last root state :=
  GeneralNominalCenteredHeadAllocBoundary.initialReorders order initial

theorem dictionaryRefl (dictionary : CommonRoleOutermostResolver.Dictionary) :
    (boundary roles).DictionaryEquivalent dictionary dictionary := rfl

end Yulang.GeneralNominalCenteredHeadAllocV7Boundary
