import Yulang.GeneralDictionaryMatStableScalar200
import Yulang.GeneralNominalCenteredHeadMatCompletionCollision

-- The known unrestricted completion counterexample is outside VariableClauses.
example : ¬ Yulang.GeneralDictionaryVariableRequirements.VariableClauses
    Yulang.GeneralNominalCenteredHeadMatCompletionCollisionSource.declaration := by
  intro restricted
  have empty := (restricted
    Yulang.GeneralNominalCenteredHeadMatCompletionCollisionSource.firstClause
    (List.mem_cons_self)).1
  cases empty

#check Yulang.GeneralNominalCenteredHeadMatStepAvailability.selected_frame
#check Yulang.GeneralNominalCenteredHeadMatStepAvailability.selected_effect
#check Yulang.GeneralNominalCenteredHeadMatCompletionCollision.not_selectedCompletion
#check Yulang.GeneralNominalCenteredHeadMatCompletionCollision.stable_selected_counterexample
