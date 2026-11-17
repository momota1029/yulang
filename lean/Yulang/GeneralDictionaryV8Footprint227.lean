import Yulang.GeneralDictionaryFirstPacketTail227
import Yulang.GeneralDictionaryHeadSharingBoundary220

/-! The finite-support and first-introduction results apply to the actual V8
boundary, not merely to a detached journal. EvidenceNode is not asserted. -/
namespace Yulang.GeneralDictionaryV8Footprint227
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal
open GeneralDictionarySemanticTrace227
open GeneralDictionarySemanticDelta223 (Depends)
open GeneralDictionaryHeadSharingBoundary220 (boundary)
open GeneralNominalCenteredHeadAllocEncoding (registry)
variable {roles : Roles.RoleDecls}

theorem reachable_footprint
    (reachable : B4TargetV8.Reachable (boundary roles) value root state) :
    ∃ context pool, GeneralNominalSourceFormation.InitialSource (registry value) context root ∧
      Footprint (registry value) context root state pool ∧ Depends state pool := by
  obtain ⟨start,initial,path⟩ := reachable
  have compiled := GeneralNominalCenteredHeadAllocBoundary.initial_compiled initial
  obtain ⟨context,labels,source,point,ground,coverage,rfl⟩ := compiled
  obtain ⟨pool,trace⟩ := from_path path
  exact ⟨context,pool,source,trace,trace.depends⟩

/-- There is one finite pool for all assignments and all future origin queries;
it is selected from the trace before any model or p0/p1 identity is supplied. -/
theorem uniform_pool
    (reachable : B4TargetV8.Reachable (boundary roles) value root state) :
    ∃ context pool, Footprint (registry value) context root state pool ∧ Depends state pool ∧
      ∀ invocation declaration purpose owner position, purpose = 0 ∨ purpose = 1 →
      fresh context.state.seed invocation declaration purpose owner position ∈ pool →
      ∃ before prior, ∃ effect : Effect roles,
        Footprint (registry value) context root before prior ∧
        fresh context.state.seed invocation declaration purpose owner position ∉ prior ∧
        Contribution (registry value) root before (install before effect)
          (GeneralDictionaryOriginJournal227.installDelta before effect) ∧
        fresh context.state.seed invocation declaration purpose owner position ∈
          GeneralDictionaryReachableRest227.packetSources effect.plan ∧
        B4Target.Steps (GeneralDictionaryDefaultKernel208.Step (registry value) root) (install before effect) state := by
  obtain ⟨context,pool,source,trace,depends⟩ := reachable_footprint reachable
  refine ⟨context,pool,trace,depends,?_⟩
  intro invocation declaration purpose owner position mergePurpose member
  exact GeneralDictionaryEffectProvenance227.first_merge_packet source trace mergePurpose member

theorem uniform_tail_pool
    (reachable : B4TargetV8.Reachable (boundary roles) value root state) :
    ∃ context pool, Footprint (registry value) context root state pool ∧ Depends state pool ∧
      ∀ invocation declaration purpose owner position, purpose = 0 ∨ purpose = 1 →
      fresh context.state.seed invocation declaration purpose owner position ∈ pool →
      ∃ before prior, ∃ effect : Effect roles,
        Footprint (registry value) context root before prior ∧
        fresh context.state.seed invocation declaration purpose owner position ∉ prior ∧
        GeneralDictionaryDefaultKernel208.Installable (registry value) before effect ∧
        Contribution (registry value) root before (install before effect)
          (GeneralDictionaryOriginJournal227.installDelta before effect) ∧
        fresh context.state.seed invocation declaration purpose owner position ∈
          GeneralDictionaryFirstPacketTail227.tailSources effect.plan ∧
        B4Target.Steps (GeneralDictionaryDefaultKernel208.Step (registry value) root) (install before effect) state := by
  obtain ⟨context,pool,source,trace,depends⟩ := reachable_footprint reachable
  refine ⟨context,pool,trace,depends,?_⟩
  intro invocation declaration purpose owner position mergePurpose member
  exact GeneralDictionaryFirstPacketTail227.first_merge_tail source trace mergePurpose member

/-- Arbitrarily many unprotected coordinates may be changed simultaneously,
with no weakening of the total journal, snapshot effects or live effects. -/
theorem patch_preserves (trace : Footprint r context root state pool)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model)
    (names : Fin count → Nat) (values : Fin count → CommonNominalFullCarrier.Ty)
    (outside : ∀ index, names index ∉ pool) :
    Models state (GeneralNominalCenteredModelExtension.assign model names values) :=
  (trace.depends model _ (GeneralNominalCenteredFrame179.assign_agree names values pool outside)).mp valid
end Yulang.GeneralDictionaryV8Footprint227
