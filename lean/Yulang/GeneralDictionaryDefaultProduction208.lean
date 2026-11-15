import Yulang.GeneralDictionaryDefaultRecorded208
import Yulang.GeneralDictionaryDefaultComposition208

namespace Yulang.GeneralDictionaryDefaultProduction208
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal
open GeneralDictionaryDefaultBoundary208
open GeneralNominalCenteredHeadMatStepAvailability (Extension)
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
  have parent : GeneralNominalSaturationState.Generated state.core.erased.current root focus :=
    reached.elim (fun same => same.symm ▸ GeneralNominalSaturationState.Generated.root) id
  have done := GeneralDictionaryDefaultRecorded208.committed reachable present
  exact .child parent (focusEq ▸ done.1.2 child (childrenEq.symm ▸ member))

theorem generated_of_fresh (checked : (boundary roles).Checked value) (effect : Effect roles)
    (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (reached : effect.plan.packet.site.occurrence = root ∨
      (boundary roles).Generated value state root effect.plan.packet.site.occurrence)
    (stable : Stable value state effect.plan.packet.site.occurrence)
    (selected : Local value state effect.plan.packet.site.occurrence
      (.selected effect.plan.packet.declaration.id children))
    (registryEq : effect.registry = GeneralNominalCenteredHeadAllocEncoding.registry value)
    (snapshot : effect.snapshot = state.core) (extension : Extension state effect)
    (member : child ∈ effect.plan.packet.children) : (boundary roles).Generated value state root child := by
  have enabled := (GeneralDictionaryDefaultAvailability208.selected_installable_iff checked reachable
    selected registryEq snapshot).mpr
    ((GeneralDictionaryDefaultLive208.extension_iff checked reachable registryEq snapshot).mp extension)
  have done := GeneralDictionaryDefaultCommitment208.enabled_stable_committed enabled stable
  have parent : GeneralNominalSaturationState.Generated state.core.erased.current root effect.plan.packet.site.occurrence :=
    reached.elim (fun same => same.symm ▸ GeneralNominalSaturationState.Generated.root) id
  exact .child parent (done.1.2 child member)

/-- Completes the existing branch unconditionally; only fresh production remains. -/
theorem generatedChildren (fresh : FreshCompletion roles) :
    B4SkeletonV7.GeneratedChildren (boundary roles) := by
  classical
  intro value checked state root focus key children reachable reached stable selected child member
  by_cases recorded : Recorded state focus key children
  · exact generated_of_recorded reachable reached recorded member
  · obtain ⟨effect,registryEq,snapshot,focusEq,keyEq,childrenEq,extension⟩ :=
      fresh value checked state root focus key children reachable reached stable selected recorded
    exact generated_of_fresh checked effect reachable (focusEq.symm ▸ reached) (focusEq.symm ▸ stable)
      (focusEq.symm ▸ keyEq.symm ▸ selected) registryEq snapshot extension (childrenEq.symm ▸ member)

/-- The exact remaining semantic obligations are named, not assumed away. -/
theorem composition (node : GeneralDictionaryDefaultComposition208.EvidenceNode roles)
    (fresh : FreshCompletion roles) :
    B4TargetV7.Statement (boundary roles) (GeneralDictionaryDefaultExecutor208.executor roles) :=
  GeneralDictionaryDefaultComposition208.composition node (generatedChildren fresh)

end Yulang.GeneralDictionaryDefaultProduction208
