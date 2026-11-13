import Yulang.GeneralDictionarySettledSourceGuard
import Yulang.GeneralNominalValueExamples

/-! Actual I26 prefix to a genuinely novel terminal output-producing child.
The parent P has further siblings; this does not settle P or resume a consumer. -/
namespace Yulang.GeneralDictionarySettledTerminalPrefix
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalSupportSiblings
open GeneralNominalDownstreamSiblingFixture
open GeneralDeclarationExamples (roles)
local instance : NeZero src.base.slots := ⟨by change 1+2 ≠ 0; omega⟩
local instance : NeZero afterP.current.context.state.base.slots := ⟨by change 1+2 ≠ 0; omega⟩

/-- The original source, not provisional producer outputs, explains this read. -/
theorem container_ready : GeneralNominalSettledSupport.ReadyAt afterP 1 := by
  let descriptor := GeneralNominalOutputGrowthModels.descriptor 1 (1 : Fin src.base.slots) (Nat.le_refl _)
  have original : Head src 1 (.nominal 0 1) (.nominal src.base 1 descriptor) :=
    Head.nominal (snapshot := src) 1 descriptor rfl
  have current : Head afterP.current.context.state 1 (.nominal 0 1) (.nominal src.base 1 descriptor) :=
    Head.nominal (snapshot := afterP.current.context.state) (1 : Fin src.base.slots) descriptor rfl
  exact ⟨_,_,current,GeneralNominalSettledSupport.source_head afterP original⟩

theorem container_decision : GeneralNominalSettledSupport.DecisionGuard reg afterP kidC := by
  have query : GeneralNominalInspection.queries afterP.current.context.state afterP.current.context.interpretation c =
      [.nominal 0 [.variables [0]]] := by
    change GeneralNominalInspection.queries src ctx.interpretation c = _
    simp [GeneralNominalInspection.queries,Declaration.normalHead,GeneralDeclarationPatterns.normalizeArgs,
      GeneralDeclarationPatterns.normalize,GeneralNominalInspection.translate,
      GeneralNominalExamples.interpretation,src,GeneralNominalOutputGrowthModels.source]
  have reads : readsMany afterP.current.context.state
      (GeneralNominalInspection.queries afterP.current.context.state afterP.current.context.interpretation c) [(1,1)] = [1] := by
    rw [query]
    simp only [readsMany.eq_def,List.append_nil]
    rw [GeneralNominalSupport.reads.eq_def]
    change (1 : Fin src.base.slots) :: readsMany afterP.current.context.state [.variables [0]] [(2,2)] = [1]
    rw [readsMany.eq_def]
    simp only [GeneralNominalSupport.reads.eq_def,readsMany.eq_def,List.append_nil]
    rfl
  constructor
  · intro index
    rw [child_inputs.1 index]
    exact container_ready
  · intro declaration visible sameRole bounds found slot member
    have same := GeneralNominalBudgetContainer.c_only declaration visible sameRole
    subst declaration
    have equal := Option.some.inj (GeneralNominalBudgetContainer.located.symm.trans found)
    subst bounds
    rw [reads] at member
    have equal := List.mem_singleton.mp member
    subst slot
    exact container_ready

theorem parent_step : GeneralNominalSettledSteps.Step reg root start afterP :=
  GeneralDictionarySettledSourceGuard.step_of_empty_facts rfl GeneralNominalValueExamples.p_first_step

theorem container_guard : GeneralNominalSettledSupport.PacketGuard afterP containerPacket [] := by
  refine ⟨GeneralNominalValueSupport.source_packet afterP containerPacket container_source_guard.1,?_⟩
  exact container_decision

theorem container_step : GeneralNominalSettledSteps.Step reg root afterP GeneralNominalBudgetContainer.afterC :=
  ⟨kidC,children_generated.1,.install containerPacket [] GeneralNominalBudgetContainer.enabled
    GeneralNominalBudgetContainer.novel container_guard⟩

theorem actual_prefix : B4Target.Steps (GeneralNominalSettledSteps.Step reg root)
    start GeneralNominalBudgetContainer.afterC :=
  .tail (.tail .refl parent_step) container_step

theorem reachable : B4TargetV5.Reachable (GeneralNominalSettledBoundary.boundary roles)
    reg root GeneralNominalBudgetContainer.afterC :=
  ⟨start,⟨ctx,initial_source,rfl⟩,actual_prefix⟩

theorem child_settled : GeneralNominalSettledSupport.PacketSettled
    GeneralNominalBudgetContainer.afterC.current containerPacket := by
  refine ⟨?_,?_⟩
  · exact List.mem_cons_self
  · intro child member
    rw [GeneralNominalBudgetContainer.children] at member
    cases member

private theorem head_has_slot {snapshot : GeneralNominalState.State} {identity test observation}
    (head : Head snapshot identity test observation) :
    ∃ slot, snapshot.base.source slot = identity := by
  cases head <;> exact ⟨_,rfl⟩

/-- The new terminal packet's output joins an actual trusted ledger. -/
theorem child_output_trusted : ∃ support,
    GeneralNominalSettledSupport.Trusted GeneralNominalBudgetContainer.afterC
      [Fact.outputs containerPacket support,Fact.inputs containerPacket support] := by
  obtain ⟨support,member⟩ := GeneralNominalSupportChoices.alternatives_exists afterP containerPacket []
    container_source_guard.1
  have input : Fact.inputs containerPacket support ∈ GeneralNominalBudgetContainer.afterC.facts := by
    apply List.mem_append_left
    apply List.mem_flatMap.mpr
    exact ⟨support,member,by simp⟩
  have output : Fact.outputs containerPacket support ∈ GeneralNominalBudgetContainer.afterC.facts := by
    apply List.mem_append_left
    apply List.mem_flatMap.mpr
    exact ⟨support,member,by simp⟩
  refine ⟨support,.output containerPacket support (.input containerPacket support .source input ?_)
    output (by simp) child_settled⟩
  intro slot member test observation head model valid
  exact GeneralCanonicalObservations.recorded_sound _ model
    (GeneralNominalBudgetContainer.source_model model valid.1).1 (head_recorded head)

/-- Fresh means beyond every original carrier slot, not a distinct semantic value. -/
theorem output_above_slots : 2 < out := GeneralNominalIdentities.source_above_seed _ _

/-- Terminal output trust does not materialize a new current observation slot. -/
theorem output_not_ready : ¬ GeneralNominalSettledSupport.ReadyAt GeneralNominalBudgetContainer.afterC out := by
  rintro ⟨test,observation,head,_⟩
  obtain ⟨slot,same⟩ := head_has_slot head
  change slot.val = out at same
  have bound := slot.isLt
  change slot.val < 3 at bound
  have above := output_above_slots
  omega

theorem inhabited : ∃ model, Models GeneralNominalBudgetContainer.afterC.current model := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,⟨model,valid,branch⟩,_⟩ := GeneralNominalBudgetContainer.enabled.1
  exact ⟨model,(GeneralNominalFeedbackSites.install_models afterP.current containerPacket
    (GeneralNominalFeedbackSites.emitted containerPacket) rfl model).mpr ⟨valid,branch⟩⟩

/-- This terminal candidate was not already committed; the existing countermodel
proves a real new output obligation, unlike the scalar empty-output leaf. -/
theorem genuine_terminal_prefix :
    GeneralNominalFeedbackSteps.Installable reg afterP.current containerPacket ∧
    ¬ GeneralNominalFeedbackSteps.Committed afterP.current containerPacket ∧
    containerPacket.children = [] ∧ kidC.demand.outputs ≠ [] ∧
    B4Target.Steps (GeneralNominalSettledSteps.Step reg root) start GeneralNominalBudgetContainer.afterC ∧
    GeneralNominalSettledSupport.PacketSettled GeneralNominalBudgetContainer.afterC.current containerPacket := by
  refine ⟨GeneralNominalBudgetContainer.enabled,GeneralNominalBudgetContainer.novel,
    GeneralNominalBudgetContainer.children,?_,actual_prefix,child_settled⟩
  rw [shared_output.1]
  simp
end Yulang.GeneralDictionarySettledTerminalPrefix
