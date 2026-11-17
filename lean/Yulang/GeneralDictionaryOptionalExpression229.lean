import Yulang.GeneralDictionaryOptionalOutput229
import Yulang.GeneralDictionaryJournalRefinement228Source
import Yulang.GeneralNominalCenteredHeadAllocMergeStable

/-! Optional-output syntax and its model-preserving refresh barrier. No
reachable optional-output journal or Stable claim is asserted here. -/
namespace Yulang.GeneralDictionaryOptionalExpression229
open GeneralDeclarationPatterns GeneralDictionaryOptionalOutput229
open GeneralDictionaryJournalRefinement228Source (constructors interpretation)
open GeneralNominalCenteredHeadMatExpressions
open CommonNominalFullCarrier

abbrev pattern : Pattern := .join (.app 3 []) (.record 0 (.app 2 []) (.app 3 []))
abbrev expression : Expr := .join (.primitive .exactEmpty [])
  (.record 0 (.primitive .emptyRecord []) (.primitive .exactEmpty []))

theorem compiled : translate constructors interpretation pattern = some expression := by
  rfl

theorem normalized : normalize pattern = pattern := by decide +kernel

theorem expression_value (variables : GeneralNominalMaterialization.Mode → Nat → Ty) (mode) :
    GeneralNominalCenteredHeadMatExpressions.value variables mode expression =
      GeneralDictionaryOptionalOutput229.value := rfl

theorem pattern_value (variables : Nat → Ty) :
    GeneralNominalCenteredHeadMatPatternSemantics.eval
      (GeneralNominalCenteredHeadMatCompilerSemantics.algebra constructors interpretation)
      variables pattern = GeneralDictionaryOptionalOutput229.value := rfl

theorem no_known {snapshot : GeneralNominalState.State}
    {model : GeneralNominalCommonBridge.Assignment} {identity : Nat}
    (valid : GeneralNominalState.Models snapshot model)
    (optional : (model identity).1 = GeneralDictionaryOptionalOutput229.value) :
    ¬ GeneralNominalState.Known snapshot identity := by
  intro known
  obtain ⟨test,observation,head⟩ := GeneralNominalCenteredHeadMatStepCache.known_has_head known
  have held := GeneralNominalCenteredHeadAllocMergeStable.head_holds head
    (GeneralCanonicalObservations.recorded_sound snapshot model valid
      (GeneralNominalSupport.head_recorded head))
  rw [optional] at held
  exact no_test test held

theorem no_refresh_known {roles : Roles.RoleDecls}
    {state : GeneralNominalCenteredHeadMatStepJournal.State roles}
    {context : GeneralNominalCandidates.Context}
    {model : GeneralNominalCommonBridge.Assignment} {identity : Nat}
    (valid : GeneralNominalCenteredHeadMatStepJournal.Models state model)
    (optional : (model identity).1 = GeneralDictionaryOptionalOutput229.value)
    (certificate : GeneralNominalCenteredHeadMatStepRefresh.Refresh state context) :
    ¬ GeneralNominalState.Known context.state identity :=
  no_known (GeneralNominalCenteredHeadMatStepRefresh.refresh_exact_transport certificate model valid) optional

end Yulang.GeneralDictionaryOptionalExpression229
