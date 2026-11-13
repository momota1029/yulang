import Yulang.GeneralDictionarySharedCurrentEvidence
import Yulang.GeneralDictionarySettledTerminalPrefix
import Yulang.GeneralNominalSharedPositive

/-! A novel terminal SharedSteps transition with current-context evidence.
Its concrete predecessor is legacy Settled-reachable; this module does not
claim a SharedSteps prefix from an initial state or resumed consumer. -/
namespace Yulang.GeneralDictionarySharedTerminalInstallation
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalSupportSiblings
open GeneralNominalDownstreamSiblingFixture
open GeneralDeclarationExamples (roles)
local instance : NeZero src.base.slots := ⟨by change 1+2 ≠ 0; omega⟩
local instance : NeZero afterP.current.context.state.base.slots := ⟨by change 1+2 ≠ 0; omega⟩

theorem container_ready : GeneralNominalSharedSupport.ReadyAt afterP 1 := by
  let descriptor := GeneralNominalOutputGrowthModels.descriptor 1 (1 : Fin src.base.slots) (Nat.le_refl _)
  have original : Head src 1 (.nominal 0 1) (.nominal src.base 1 descriptor) :=
    Head.nominal (snapshot := src) 1 descriptor rfl
  have current : Head afterP.current.context.state 1 (.nominal 0 1) (.nominal src.base 1 descriptor) :=
    Head.nominal (snapshot := afterP.current.context.state) (1 : Fin src.base.slots) descriptor rfl
  exact ⟨_,_,current,GeneralNominalSharedSupport.source_head afterP original⟩

theorem container_decision : GeneralNominalSharedSupport.DecisionGuard reg afterP kidC := by
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


theorem container_guard : GeneralNominalSharedSteps.PacketGuard afterP containerPacket [] := by
  apply GeneralNominalSharedSteps.leaf_guard rfl
    (GeneralNominalSharedPositive.leaf_input_coherent containerPacket rfl)
    (GeneralNominalValueSupport.source_packet afterP containerPacket container_source_guard.1)
  exact container_decision

noncomputable def after := GeneralNominalSharedSteps.install afterP containerPacket []

theorem step : GeneralNominalSharedSteps.Step reg root afterP after :=
  ⟨kidC,children_generated.1,.install containerPacket [] GeneralNominalBudgetContainer.enabled
    GeneralNominalBudgetContainer.novel container_guard⟩

theorem inhabited : ∃ model, Models after.current model := by
  exact ⟨journalModel,(GeneralNominalSharedSteps.install_models (packet := containerPacket)
    (state := afterP) (support := []) rfl journalModel).mpr
      ⟨GeneralNominalBudgetContainer.source_model journalModel cut_journal_models.1,
       GeneralNominalBudgetContainer.journal_branch⟩⟩

/-- No child evidence hypotheses are needed for this actual terminal packet. -/
theorem current_dictionary (model : GeneralNominalCommonBridge.Assignment)
    (valid : Models after.current model) :
    GeneralDictionaryRecursiveEvidence.Evidence reg after.current.context model kidC
      (.node c.id []) :=
  GeneralDictionarySharedCurrentEvidence.terminal_current_evidence containerPacket []
    GeneralNominalBudgetContainer.enabled GeneralNominalBudgetContainer.children model valid

theorem genuine_terminal_step :
    GeneralNominalSharedSteps.Step reg root afterP after ∧
    (∃ model, Models after.current model) ∧
    ∀ model, Models after.current model →
      GeneralDictionaryRecursiveEvidence.Evidence reg after.current.context model kidC (.node c.id []) :=
  ⟨step,inhabited,current_dictionary⟩

end Yulang.GeneralDictionarySharedTerminalInstallation
