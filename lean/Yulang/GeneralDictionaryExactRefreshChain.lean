import Yulang.GeneralDictionaryTerminalRefreshObstruction

/-! Finite chains of genuine context regeneration with exact Refresh certificates.
This is a certificate-level relation, not a claim of generated-root scheduling:
actual scheduled refreshes also require focus/unknown/known side conditions.
The obstruction covers every such chain, even without those extra restrictions.
Installations/learned constraints are deliberately not included. -/
namespace Yulang.GeneralDictionaryExactRefreshChain
open GeneralNominalSaturationState
open GeneralNominalCommonBridge (Assignment)

inductive ExactRefresh : State roles → State roles → Prop
  | update (before : State roles) (next : GeneralNominalCandidates.Context)
      (certificate : GeneralNominalFeedbackSteps.Refresh before next) :
      ExactRefresh before (regenerate before next)

theorem step_models (step : ExactRefresh before after) (model : Assignment) :
    Models after model ↔ Models before model := by
  cases step with
  | update next certificate => exact GeneralNominalCycleSteps.refresh_models certificate model

theorem chain_models (path : B4Target.Steps ExactRefresh before after)
    (model : Assignment) : Models after model ↔ Models before model := by
  induction path with
  | refl => exact Iff.rfl
  | tail previous step ih => exact (step_models step model).trans ih

/-- Both incompatible output models survive every exact regeneration chain. -/
theorem terminal_unknown (after : State GeneralDeclarationExamples.roles)
    (path : B4Target.Steps ExactRefresh GeneralNominalBudgetContainer.afterC.current after) :
    ¬ GeneralNominalState.Known after.context.state GeneralNominalSupportSiblings.out := by
  apply GeneralDictionaryTerminalRefreshObstruction.no_known
  · exact ((chain_models path _).mpr GeneralDictionaryTerminalRefreshObstruction.int_model).1
  · exact ((chain_models path _).mpr GeneralDictionaryTerminalRefreshObstruction.nominal_model).1

/-- A genuinely informative future state must exclude at least one witness.
This states a necessary constraint, not a fabricated learned constraint or a
proof that excluding one witness suffices for readiness. -/
theorem known_requires_model_exclusion (after : State GeneralDeclarationExamples.roles)
    (known : GeneralNominalState.Known after.context.state GeneralNominalSupportSiblings.out) :
    ¬ (Models after (GeneralNominalOutputGrowth.finiteModel 1) ∧
       Models after GeneralNominalDownstreamSiblingFixture.journalModel) := by
  rintro ⟨one,two⟩
  exact GeneralDictionaryTerminalRefreshObstruction.no_known after.context.state one.1 two.1 known

end Yulang.GeneralDictionaryExactRefreshChain
