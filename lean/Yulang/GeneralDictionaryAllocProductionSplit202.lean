import Yulang.GeneralDictionaryAllocRecordedChildren202
import Yulang.GeneralDictionarySelectedInterface202
import Yulang.GeneralNominalCenteredHeadAllocV7Composition
import Yulang.GeneralNominalCenteredHeadAllocV7Completion

namespace Yulang.GeneralDictionaryAllocProductionSplit202
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal
open GeneralNominalCenteredHeadAllocV7Boundary
open GeneralNominalCenteredHeadMatStepAvailability (Extension)
open GeneralDictionaryAllocRecordedChildren202
variable {roles : Roles.RoleDecls}

/-- Exact children, including order and multiplicity; no model in this test. -/
def Recorded (state : State roles) (focus : Occurrence roles) (key : Nat)
    (children : List (Occurrence roles)) : Prop :=
  ∃ plan ∈ state.core.plans, plan.packet.site.occurrence = focus ∧
    plan.packet.declaration.id = key ∧ plan.packet.children = children

/-- A remaining obligation, not an assertion that fresh production is total. -/
def FreshCompletion (roles : Roles.RoleDecls) : Prop :=
  ∀ value, (boundary roles).Checked value → ∀ state root focus key children,
    B4TargetV7.Reachable (boundary roles) value root state →
    (focus = root ∨ (boundary roles).Generated value state root focus) →
    Stable value state focus → Local value state focus (.selected key children) →
    ¬ Recorded state focus key children →
    ∃ effect : Effect roles, effect.registry = GeneralNominalCenteredHeadAllocEncoding.registry value ∧
      effect.snapshot = state.core ∧ effect.plan.packet.site.occurrence = focus ∧
      effect.plan.packet.declaration.id = key ∧ effect.plan.packet.children = children ∧ Extension state effect

theorem generated_of_recorded
    (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (reached : focus = root ∨ (boundary roles).Generated value state root focus)
    (recorded : Recorded state focus key children) (member : child ∈ children) :
    (boundary roles).Generated value state root child := by
  obtain ⟨plan,present,focusEq,_,childrenEq⟩ := recorded
  exact v7_recorded_generated reachable present (focusEq.symm ▸ reached) (childrenEq.symm ▸ member)

theorem generated_of_fresh (effect : Effect roles)
    (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (reached : effect.plan.packet.site.occurrence = root ∨
      (boundary roles).Generated value state root effect.plan.packet.site.occurrence)
    (stable : Stable value state effect.plan.packet.site.occurrence)
    (selected : Local value state effect.plan.packet.site.occurrence
      (.selected effect.plan.packet.declaration.id children))
    (registryEq : effect.registry = GeneralNominalCenteredHeadAllocEncoding.registry value)
    (snapshot : effect.snapshot = state.core) (extension : Extension state effect)
    (member : child ∈ effect.plan.packet.children) : (boundary roles).Generated value state root child := by
  have done := GeneralNominalCenteredHeadMatStepAvailability.stable_focus_selected_committed
    (GeneralNominalCenteredHeadAllocBoundary.reachable_compiled reachable) stable
    (GeneralNominalCenteredHeadAllocBoundary.local_iff.mp (B4TargetV7.selected_iff.mp selected).1)
    registryEq snapshot extension
  have parent : GeneralNominalSaturationState.Generated state.core.erased.current root effect.plan.packet.site.occurrence :=
    reached.elim (fun same => same.symm ▸ GeneralNominalSaturationState.Generated.root) id
  exact .child parent (done.2 child member)

/-- Completes the existing branch unconditionally; only fresh production remains. -/
theorem generatedChildren (fresh : FreshCompletion roles) :
    B4SkeletonV7.GeneratedChildren (boundary roles) := by
  classical
  intro value checked state root focus key children reachable reached stable selected child member
  by_cases recorded : Recorded state focus key children
  · exact generated_of_recorded reachable reached recorded member
  · obtain ⟨effect,registryEq,snapshot,focusEq,keyEq,childrenEq,extension⟩ :=
      fresh value checked state root focus key children reachable reached stable selected recorded
    exact generated_of_fresh effect reachable (focusEq.symm ▸ reached) (focusEq.symm ▸ stable)
      (focusEq.symm ▸ keyEq.symm ▸ selected) registryEq snapshot extension (childrenEq.symm ▸ member)

theorem fresh_of_global (completion : GeneralNominalCenteredHeadAllocV7Completion.SelectedCompletion roles) :
    FreshCompletion roles :=
  fun value checked state root focus key children reachable _ _ selected _ =>
    completion value checked state root focus key children reachable selected

/-- This remains conditional on the exact I34 node law and fresh production. -/
theorem composition
    (node : GeneralDictionarySelectedInterface202.SelectedEvidenceNode
      (GeneralNominalCenteredHeadAllocBoundary.boundary roles))
    (fresh : FreshCompletion roles) :
    B4TargetV7.Statement (boundary roles) (GeneralNominalCenteredHeadAllocV7Executor.executor roles) :=
  GeneralNominalCenteredHeadAllocV7Composition.composition
    (GeneralDictionarySelectedInterface202.to_v7 _ node) (generatedChildren fresh)

end Yulang.GeneralDictionaryAllocProductionSplit202
