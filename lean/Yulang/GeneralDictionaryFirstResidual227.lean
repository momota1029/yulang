import Yulang.GeneralDictionaryEmittedFootprint227

/-! Concrete residual list for the first protected p0/p1 occurrence. Actual
emitted RHS reads, head-schema reads and live class effects have been removed;
raw merges, emitted targets/range reads and child support remain. -/
namespace Yulang.GeneralDictionaryFirstResidual227
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal GeneralDictionaryDefaultKernel208
open GeneralDictionarySemanticTrace227 GeneralDictionaryOriginJournal227
open GeneralNominalCenteredHeadMatPlans (emittedSchema)
open GeneralDictionaryDefaultTotalFrame212 (resolve)
variable {roles : Roles.RoleDecls}

def emittedResidual (plan : Plan roles) : List Nat :=
  (emittedSchema plan).equations.flatMap fun equation =>
    equation.target :: (if equation.mode = .actual then [] else
      GeneralDictionaryDefaultModeSupport212.reads (resolve plan) equation.mode equation.expression)

def ResidualSources (plan : Plan roles) : List Nat :=
  GeneralDictionaryReachablePacket226.mergeSources plan ++ emittedResidual plan ++
    GeneralDictionaryDefaultPacketSupport213.childSources plan

theorem tail_prior_or_residual
    (trace : Footprint registry context root before pool)
    (enabled : Installable registry before effect)
    (notTwo : purpose ≠ 2) (notEight : purpose ≠ 8)
    (member : fresh context.state.seed invocation declaration purpose owner position ∈
      GeneralDictionaryFirstPacketTail227.tailSources effect.plan) :
    fresh context.state.seed invocation declaration purpose owner position ∈ pool ∨
    fresh context.state.seed invocation declaration purpose owner position ∈ ResidualSources effect.plan := by
  rcases List.mem_append.mp member with mergeEmitted | child
  · rcases List.mem_append.mp mergeEmitted with merges | emitted
    · exact Or.inr (by simp [ResidualSources,merges])
    · obtain ⟨model,valid,branch,_⟩ := enabled.common
      have head := (GeneralNominalCenteredHeadMatStepPackets.head_equations branch).2.2
      rcases GeneralDictionaryEmittedFootprint227.schema_residual trace effect.plan
        (GeneralDictionaryDefaultDepth208.frame enabled) model valid head notTwo notEight emitted with old | residual
      · exact Or.inl old
      · obtain ⟨equation,present,targetOrRange⟩ := residual
        have within : fresh context.state.seed invocation declaration purpose owner position ∈ emittedResidual effect.plan := by
          apply List.mem_flatMap.mpr
          refine ⟨equation,present,?_⟩
          rcases targetOrRange with target | ⟨nonactual,read⟩
          · exact List.mem_cons.mpr (Or.inl target)
          · exact List.mem_cons.mpr (Or.inr (by simpa only [nonactual,ite_false] using read))
        exact Or.inr (by simp [ResidualSources,within])
  · exact Or.inr (by simp [ResidualSources,child])

/-- The concrete first-use residual retains the actual enabled event, its
prior footprint absence, and the suffix of the original run. -/
theorem first_merge_residual
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (trace : Footprint registry context root state pool)
    (mergePurpose : purpose = 0 ∨ purpose = 1)
    (present : fresh context.state.seed invocation declaration purpose owner position ∈ pool) :
    ∃ before prior, ∃ effect : Effect roles,
      Footprint registry context root before prior ∧
      fresh context.state.seed invocation declaration purpose owner position ∉ prior ∧
      Installable registry before effect ∧
      Contribution registry root before (install before effect) (installDelta before effect) ∧
      fresh context.state.seed invocation declaration purpose owner position ∈ ResidualSources effect.plan ∧
      B4Target.Steps (Step registry root) (install before effect) state := by
  obtain ⟨before,prior,effect,history,absent,enabled,event,member,suffix⟩ :=
    GeneralDictionaryFirstPacketTail227.first_merge_tail source trace mergePurpose present
  have residual := (tail_prior_or_residual history enabled (by omega) (by omega) member).resolve_left absent
  exact ⟨before,prior,effect,history,absent,enabled,event,residual,suffix⟩

end Yulang.GeneralDictionaryFirstResidual227
