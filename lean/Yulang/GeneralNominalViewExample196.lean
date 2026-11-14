import Yulang.GeneralNominalVariableView196
import Yulang.GeneralNominalExamples
import Yulang.GeneralDictionaryOrdinaryTrace

set_option backward.isDefEq.respectTransparency false
/-! Inhabited descriptor-change regression. This is a context transformation,
not an asserted executable refresh: its all-model certificate is not supplied. -/
namespace Yulang.GeneralNominalViewExample196
open GeneralNominalViewTransport196
open GeneralNominalExamples (state interpretation listDescriptor model state_models)

abbrev beforeState : GeneralNominalState.State :=
  { state true with nominals := fun _ => none, catalogue := (by intro _ _ h; cases h), bodies_opaque := (by intro _ _ h; cases h) }
abbrev before : GeneralNominalCandidates.Context := ⟨beforeState,interpretation⟩
def next : View beforeState :=
  ⟨(state true).view,(state true).nominals,(state true).catalogue,(state true).bodies_opaque⟩
abbrev after := context before next
abbrev declaration : GeneralDeclarations.Declaration := ⟨900,0,[.var 0],[],[],[]⟩

theorem descriptor_changed : before.state.nominals 0 = none ∧
    after.state.nominals ⟨0,by decide⟩ = some listDescriptor := ⟨rfl,rfl⟩

theorem before_models : GeneralNominalState.Models before.state model := by
  have valid := state_models true
  exact ⟨valid.1,(by intro _ _ h; cases h),valid.2.2⟩

theorem after_models : GeneralNominalState.Models after.state model := state_models true

theorem variable_query : GeneralNominalInspection.queries before.state before.interpretation declaration =
    [GeneralNominalInspection.Query.variables [0]] := by
  simp [GeneralNominalInspection.queries, GeneralDeclarations.Declaration.normalHead,
    GeneralDeclarationPatterns.normalizeArgs, GeneralDeclarationPatterns.normalize, GeneralNominalInspection.translate]

theorem rechecked (bounds : List (GeneralNominalInspection.Bounds before.state)) :
    Rechecked before next declaration bounds :=
  GeneralNominalVariableView196.rechecked_variables before next declaration [[0]] variable_query bounds

theorem not_ordinary_extension : ¬ GeneralDictionaryOrdinaryTrace.Extension before after := by
  rintro ⟨reserved,atoms,allocated,same⟩
  have empty : ∀ slot, (GeneralDictionaryOrdinaryTrace.extendContext before reserved atoms allocated).state.nominals slot = none := by
    intro slot
    rfl
  rw [← same] at empty
  have impossible := empty ⟨0,by decide⟩
  change some listDescriptor = none at impossible
  cases impossible

/-- A nonvacuous change outside the ordinary-growth relation with exact finite
reinspection agreement, including nonempty lists of source bounds. -/
theorem inhabited_change : before.state.nominals 0 ≠ after.state.nominals ⟨0,by decide⟩ ∧
    GeneralNominalState.Models before.state model ∧ GeneralNominalState.Models after.state model ∧
    Rechecked before next declaration [(0,0),(1,1)] ∧
    ¬ GeneralDictionaryOrdinaryTrace.Extension before after :=
  by
  refine ⟨?_,before_models,after_models,rechecked _,not_ordinary_extension⟩
  intro h
  cases h
end Yulang.GeneralNominalViewExample196
