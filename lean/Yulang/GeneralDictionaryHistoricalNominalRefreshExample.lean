import Yulang.GeneralDictionaryHistoricalNominalCoverage
import Yulang.GeneralDictionaryUnaryCurrentExample

/-! Historical coverage on the actual mixed packet's 2-to-3-slot Value refresh.
The nominal query has a nonempty capture. Selection is not inferred from history:
the selected adapter retains its explicit selection premise. -/
namespace Yulang.GeneralDictionaryHistoricalNominalRefreshExample
open GeneralDictionaryMixedCatalogExample GeneralDictionaryMixedCarrierRefresh
open GeneralNominalExamples (displayRoot model)
open GeneralNominalSaturationState GeneralNominalRecursiveCandidates
open GeneralDictionaryRecursiveEvidence GeneralDictionaryNestedRefinement

theorem scope : NominalOnlyMany (GeneralNominalInspection.queries packet.context.state
    packet.context.interpretation packet.declaration) := by
  rw [GeneralDictionaryMixedCatalogInhabited.query]
  exact ⟨⟨True.intro,True.intro⟩,True.intro⟩

theorem supported : GeneralDictionaryHistoricalNominalCoverage.Supported refreshed displayRoot :=
  GeneralDictionaryHistoricalNominalCoverage.supported_of_recorded packet refreshed packet_recorded
    GeneralDictionaryUnaryCurrentExample.prior scope

theorem current_instance (m : GeneralNominalCommonBridge.Assignment) (valid : Models refreshed.current m) :
    Instance registry refreshedContext m displayRoot declaration.id GeneralDictionaryUnaryCurrentExample.children :=
  GeneralDictionaryNestedCurrentEvidence.current_instance packet displayRoot refreshed refreshed_reachable
    packet_recorded GeneralDictionaryUnaryCurrentExample.prior rfl scope m valid

theorem positive_coverage :
    B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary GeneralDeclarationExamples.roles)
      registry displayRoot refreshed ∧
    GeneralDictionaryHistoricalNominalCoverage.Supported refreshed displayRoot ∧
    Models refreshed.current model ∧
    Instance registry refreshedContext model displayRoot declaration.id GeneralDictionaryUnaryCurrentExample.children ∧
    GeneralDictionaryUnaryCurrentExample.children ≠ [] :=
  ⟨refreshed_reachable,supported,refreshed_inhabited,current_instance model refreshed_inhabited,
    GeneralDictionaryUnaryCurrentExample.nonterminal⟩

theorem capture_nonempty : currentReport.captures ≠ [] := by
  rw [report_current]
  intro impossible
  cases impossible

theorem selected_instance (key : Nat) (children : List (GeneralSourceDictionaries.Occurrence GeneralDeclarationExamples.roles))
    (selected : GeneralNominalValueBoundary.Local registry refreshed displayRoot (.selected key children))
    (m : GeneralNominalCommonBridge.Assignment) (valid : Models refreshed.current m) :
    Instance registry refreshedContext m displayRoot key children :=
  GeneralDictionaryHistoricalNominalCoverage.selected_instance registry displayRoot displayRoot refreshed
    refreshed_reachable supported key children selected m valid
theorem selected_evidence (key : Nat) (children : List (GeneralSourceDictionaries.Occurrence GeneralDeclarationExamples.roles))
    (selected : GeneralNominalValueBoundary.Local registry refreshed displayRoot (.selected key children))
    (m : GeneralNominalCommonBridge.Assignment) (valid : Models refreshed.current m)
    (dictionaries : List GeneralDictionaryReadback.Payload)
    (given : CommonRoleOutermostResolver.All₂ (Evidence registry refreshedContext m) children dictionaries) :
    Evidence registry refreshedContext m displayRoot (.node key dictionaries) :=
  evidence_node registry refreshedContext m displayRoot key children dictionaries
    (selected_instance key children selected m valid) given

end Yulang.GeneralDictionaryHistoricalNominalRefreshExample
