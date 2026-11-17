import Yulang.GeneralDictionaryFirstExtreme228
import Yulang.GeneralDictionaryV8Footprint227

namespace Yulang.GeneralDictionaryV8Extreme228
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal GeneralDictionarySemanticTrace227
open GeneralDictionarySemanticDelta223 (Depends)
open GeneralDictionaryHeadSharingBoundary220 (boundary)
open GeneralNominalCenteredHeadAllocEncoding (registry)
open GeneralDictionaryV8Footprint227 (reachable_footprint)
variable {roles : Roles.RoleDecls}

theorem uniform_local_or_extreme_pool
    (reachable : B4TargetV8.Reachable (boundary roles) value root state) :
    ∃ context pool, Footprint (registry value) context root state pool ∧ Depends state pool ∧
      ∀ invocation declaration purpose owner position, purpose = 0 ∨ purpose = 1 →
      fresh context.state.seed invocation declaration purpose owner position ∈ pool →
      ∃ before prior, ∃ effect : Effect roles, ∃ model : GeneralNominalCommonBridge.Assignment,
        Footprint (registry value) context root before prior ∧
        fresh context.state.seed invocation declaration purpose owner position ∉ prior ∧
        GeneralDictionaryDefaultKernel208.Installable (registry value) before effect ∧ Models before model ∧
        GeneralNominalCenteredHeadMatStepPackets.Holds effect.plan model ∧
        Contribution (registry value) root before (install before effect)
          (GeneralDictionaryOriginJournal227.installDelta before effect) ∧
        (GeneralDictionaryResidualOwnership228.LocalMerge effect.plan
          (fresh context.state.seed invocation declaration purpose owner position) ∨
         GeneralDictionaryFirstExtreme228.Extreme effect.plan model
          (fresh context.state.seed invocation declaration purpose owner position)) ∧
        B4Target.Steps (GeneralDictionaryDefaultKernel208.Step (registry value) root) (install before effect) state := by
  obtain ⟨context,pool,source,trace,depends⟩ := reachable_footprint reachable
  refine ⟨context,pool,trace,depends,?_⟩
  intro invocation declaration purpose owner position mergePurpose member
  exact GeneralDictionaryFirstExtreme228.first_local_or_extreme source trace mergePurpose member

end Yulang.GeneralDictionaryV8Extreme228
