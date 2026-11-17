import Yulang.GeneralDictionaryOptionalSelected229

/-! Reachable optional-output selection without a current Instance, plus a
precise obstruction to refreshing source4. Global Stable remains unproved:
other administrative updates and generated identities are not excluded. -/
namespace Yulang.GeneralDictionaryOptionalRegression229
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229 GeneralDictionaryOptionalInstall229
open GeneralDictionaryOptionalStage229 GeneralDictionaryOptionalSelected229

theorem no_output_refresh (context : GeneralNominalCandidates.Context)
    (certificate : GeneralNominalCenteredHeadMatStepRefresh.Refresh stage context) :
    ¬ GeneralNominalState.Known context.state 4 :=
  GeneralDictionaryOptionalExpression229.no_refresh_known stage_model rfl certificate

theorem no_lower_refresh (context : GeneralNominalCandidates.Context)
    (certificate : GeneralNominalCenteredHeadMatStepRefresh.Refresh stage context) :
    ¬ GeneralNominalState.Known context.state lo :=
  GeneralDictionaryOptionalExpression229.no_refresh_known stage_model lower_value certificate

theorem selected_without_instance :
    B4TargetV8.Reachable (GeneralDictionaryHeadSharingBoundary220.boundary roles) sourceRegistry root stage ∧
    GeneralNominalCenteredHeadMatStepJournal.Models stage model ∧
    GeneralDictionaryHeadSharingBoundary220.Local sourceRegistry stage root
      (.selected declaration.id currentPacket.children) ∧
    ¬ GeneralDictionaryTotalEvidence206.Instance registry stage.core model root declaration.id currentPacket.children :=
  ⟨GeneralDictionaryOptionalReachable229.reachable,stage_model,selected,no_instance⟩

/-- This eliminates the *particular* exact-head completion that resolves the
exact-empty probe. It is deliberately weaker than global stability. -/
theorem output_refresh_barrier :
    ∀ context, GeneralNominalCenteredHeadMatStepRefresh.Refresh stage context →
      ¬ GeneralNominalState.Known context.state 4 ∧
      ¬ GeneralNominalState.Known context.state lo :=
  fun context certificate => ⟨no_output_refresh context certificate,no_lower_refresh context certificate⟩

end Yulang.GeneralDictionaryOptionalRegression229
