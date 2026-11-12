# Cycle151 exact quantified theorem types

```text
  Yulang.GeneralDictionaryVariableTreeExample.children
Yulang.GeneralDictionaryVariableTreeInstallation.packet_children : @Eq
  (List (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles))
  (@Yulang.GeneralNominalSaturationState.Packet.children Yulang.GeneralDeclarationExamples.roles
    Yulang.GeneralDictionaryVariableTreeInstallation.packet)
  Yulang.GeneralDictionaryVariableTreeExample.children
Yulang.GeneralDictionaryVariableTreeInstallation.enabled : @Yulang.GeneralNominalFeedbackSteps.Installable
  Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryVariableTreeExample.registry
  (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
    Yulang.GeneralDictionaryVariableTreeExample.start)
  Yulang.GeneralDictionaryVariableTreeInstallation.packet
Yulang.GeneralDictionaryVariableTreeInstallation.novel : Not
  (@Yulang.GeneralNominalFeedbackSteps.Committed Yulang.GeneralDeclarationExamples.roles
    (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
      Yulang.GeneralDictionaryVariableTreeExample.start)
    Yulang.GeneralDictionaryVariableTreeInstallation.packet)
Yulang.GeneralDictionaryVariableTreeInstallation.guard : @Yulang.GeneralNominalSupportSteps.PacketGuard
  Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryVariableTreeExample.start
  Yulang.GeneralDictionaryVariableTreeInstallation.packet
  (@List.nil (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles))
Yulang.GeneralDictionaryVariableTreeInstallation.install_at : @Yulang.GeneralNominalSupportSteps.At
  Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryVariableTreeExample.registry
  Yulang.GeneralDictionaryVariableTreeExample.start Yulang.GeneralNominalBranchExample.root
  Yulang.GeneralDictionaryVariableTreeInstallation.installed
Yulang.GeneralDictionaryVariableTreeInstallation.install_step : @Yulang.GeneralNominalSupportSteps.Step
  Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryVariableTreeExample.registry
  Yulang.GeneralNominalBranchExample.root Yulang.GeneralDictionaryVariableTreeExample.start
  Yulang.GeneralDictionaryVariableTreeInstallation.installed
Yulang.GeneralDictionaryVariableTreeInstallation.not_stable : Not
  (@Yulang.GeneralNominalSupportSteps.Stable Yulang.GeneralDeclarationExamples.roles
    Yulang.GeneralDictionaryVariableTreeExample.registry Yulang.GeneralDictionaryVariableTreeExample.start
    Yulang.GeneralNominalBranchExample.root)
Yulang.GeneralDictionaryVariableTreeSelected.other_failed : ∀
  (check :
    Yulang.GeneralDeclarations.DeclarationChecked Yulang.GeneralDictionaryVariableTreeExample.registry.constructors
      Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryVariableTreeExample.leafDeclaration),
  @Yulang.GeneralNominalRecursiveCandidates.Failed Yulang.GeneralDeclarationExamples.roles
    Yulang.GeneralDictionaryVariableTreeExample.registry Yulang.GeneralNominalBranchExample.context
    Yulang.GeneralNominalBranchExample.root Yulang.GeneralDictionaryVariableTreeExample.leafDeclaration check
Yulang.GeneralDictionaryVariableTreeSelected.not_mixed_recurs : ∀
  (slot : Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))),
  Not (Yulang.GeneralNominalMixedRecurrence.RecursAt Yulang.GeneralNominalBranchExample.state slot)
Yulang.GeneralDictionaryVariableTreeSelected.selected : @Yulang.GeneralNominalFeedbackK2.Local
  Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryVariableTreeExample.registry
  (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
    Yulang.GeneralDictionaryVariableTreeExample.start)
  Yulang.GeneralNominalBranchExample.root
  (@Yulang.CommonRoleOutermostResolver.Frontier.selected
    (Yulang.GeneralNominalCycleBoundary.vocabulary Yulang.GeneralDeclarationExamples.roles).Demand
    Yulang.GeneralDictionaryVariableTreeExample.declaration.id Yulang.GeneralDictionaryVariableTreeExample.children)
Yulang.GeneralDictionaryVariableTreeSelected.decisions : @Yulang.GeneralNominalSupport.DecisionGuard
  Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryVariableTreeExample.start
  Yulang.GeneralDictionaryVariableTreeExample.registry Yulang.GeneralNominalBranchExample.root
  (@List.nil (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles))
Yulang.GeneralDictionaryVariableTreeSelected.support_selected : @Yulang.GeneralNominalSupportBoundary.Local
  Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryVariableTreeExample.registry
  Yulang.GeneralDictionaryVariableTreeExample.start Yulang.GeneralNominalBranchExample.root
  (@Yulang.CommonRoleOutermostResolver.Frontier.selected
    (Yulang.GeneralNominalSupportBoundary.vocabulary Yulang.GeneralDeclarationExamples.roles).Demand
    Yulang.GeneralDictionaryVariableTreeExample.declaration.id Yulang.GeneralDictionaryVariableTreeExample.children)

```
