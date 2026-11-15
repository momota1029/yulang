import Yulang.GeneralDictionaryDefaultKernel208
import Yulang.GeneralDictionaryDefaultGap206Counterexample
import Yulang.GeneralNominalCenteredHeadMatCompletionLive

set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralDictionaryDefaultRegression208
open GeneralDictionaryDefaultGap206Source GeneralDictionaryDefaultGap206Local
open GeneralDictionaryDefaultGap206State
open GeneralNominalCenteredHeadMatStepJournal

noncomputable def effect : Effect roles := ⟨registry,start.core,plan,frame,unique,ready⟩
noncomputable def after : State roles := install start effect

theorem enabled : GeneralDictionaryDefaultKernel208.Installable registry start effect := by
  apply (GeneralNominalCenteredHeadMatCompletionLive.selected_installable_iff checked reachable selected rfl rfl).mpr
  refine ⟨?_,model,inhabited,total_packet model inhabited,head_equations,class_effects⟩
  intro prior member
  cases member

theorem not_committed : ¬ GeneralDictionaryDefaultKernel208.Committed start plan := by
  intro committed
  have effects := GeneralDictionaryDefaultKernel208.committed_class committed counter_inhabited
  have certificate := GeneralDictionaryTotalEvidence206.certificate_of_semantics frame rfl
    (total_packet counter counter_inhabited) ready effects
  exact GeneralDictionaryDefaultGap206Counterexample.no_default_output
    (certificate.outputs ⟨0,0⟩ (List.mem_singleton_self _))

theorem step : GeneralDictionaryDefaultKernel208.Step registry root start after :=
  ⟨root,.root,.install effect enabled not_committed⟩

theorem no_longer_stable : ¬ GeneralDictionaryDefaultKernel208.Stable registry start root :=
  fun stable => stable root .root after (.install effect enabled not_committed)

theorem default_installed : GeneralDictionaryDefaultKernel208.Committed after plan :=
  GeneralDictionaryDefaultKernel208.installed_committed (effect := effect) rfl

theorem bottom_removed : ¬ Models after counter := by
  intro valid
  have effects := (install_models (state := start) (effect := effect) rfl).mp valid |>.2.2.1.2
  have certificate := GeneralDictionaryTotalEvidence206.certificate_of_semantics frame rfl
    (total_packet counter counter_inhabited) ready effects
  exact GeneralDictionaryDefaultGap206Counterexample.no_default_output
    (certificate.outputs ⟨0,0⟩ (List.mem_singleton_self _))

theorem int_retained : Models after model :=
  GeneralNominalCenteredHeadMatCompletionLive.common_successor_model checked reachable rfl rfl
    inhabited (total_packet model inhabited) ⟨head_equations,class_effects⟩

/-- This regression distinguishes a new justified install from old no-op commitment. -/
theorem genuine_change : GeneralNominalCenteredHeadMatStepKernel.Committed start plan ∧
    ¬ GeneralDictionaryDefaultKernel208.Committed start plan ∧
    GeneralDictionaryDefaultKernel208.Step registry root start after ∧
    Models after model ∧ ¬ Models after counter :=
  ⟨committed,not_committed,step,int_retained,bottom_removed⟩

end Yulang.GeneralDictionaryDefaultRegression208
