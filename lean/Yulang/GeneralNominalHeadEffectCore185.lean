import Yulang.GeneralNominalHeadEffectsOrigin185
import Yulang.GeneralNominalHeadLedgerFrame182

/-! The head part of every recorded effect is already covered by the actual
core plan ledger. Snapshot/live output schemas remain separate support. -/
namespace Yulang.GeneralNominalHeadEffectCore185
open GeneralNominalCenters GeneralSourceDictionaries
open GeneralNominalCenteredHeadStepEffects
open GeneralNominalHeadLedgerFrame182
variable {roles : Roles.RoleDecls}

theorem head_sources_subset (plan : Plan roles) :
    headSources plan ⊆ GeneralNominalModeLedger181.equationSources plan := by
  intro name member
  rcases List.mem_append.mp member with member | member
  · rcases List.mem_append.mp member with member | member
    · simp only [GeneralNominalModeLedger181.equationSources,List.mem_append]
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl member))))
    · obtain ⟨binder,named,within⟩ := List.mem_flatMap.mp member
      have capture : name ∈ GeneralNominalCenteredFrame179.captureSources plan :=
        List.mem_flatMap.mpr ⟨binder,(GeneralNominalCenteredFrame179.capture_mem plan binder).mpr (Or.inl named),within⟩
      simp only [GeneralNominalModeLedger181.equationSources,List.mem_append]
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr capture))))
  · simp only [GeneralNominalModeLedger181.equationSources,List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inr member)))

theorem effect_plan_registered
    (reachable : B4TargetV6.Reachable (GeneralNominalCenteredHeadWFBoundary.boundary roles) registry root state)
    (effect : Effect roles) (member : effect ∈ state.effects) : effect.plan ∈ state.core.plans := by
  rw [GeneralNominalHeadEffectsOrigin185.wf_plans_effects reachable]
  exact List.mem_map.mpr ⟨effect,member,rfl⟩

theorem effect_head_in_core
    (reachable : B4TargetV6.Reachable (GeneralNominalCenteredHeadWFBoundary.boundary roles) registry root state)
    (effect : Effect roles) (member : effect ∈ state.effects) :
    headSources effect.plan ⊆ GeneralNominalModeLedger181.fullSources state.core := by
  intro name present
  exact List.mem_append_right _ (List.mem_append_right _ (List.mem_flatMap.mpr
    ⟨effect.plan,effect_plan_registered reachable effect member,head_sources_subset effect.plan present⟩))

end Yulang.GeneralNominalHeadEffectCore185
