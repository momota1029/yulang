import Yulang.GeneralDictionaryRequestCatalogCompute
import Yulang.GeneralDictionaryMixedCatalogReachable

/-! Exact computed filtering for the mixed emitted request list. The operational
reachability result remains the separately proved real installation theorem. -/
namespace Yulang.GeneralDictionaryComputedCatalogExample
open GeneralDictionaryMixedCatalogExample
open GeneralDictionaryRequestCatalogCompute
open GeneralNominalMaterialization

theorem packet_computed : packetRequests packet = [closedRequest] := by
  unfold packetRequests
  rw [emissions]
  simp [generated,closedRequest,openRequest,GeneralNominalInspection.translate,
    GeneralNominalExamples.interpretation,GeneralDeclarationPatterns.normalize,
    GeneralDeclarationPatterns.normalizeArgs,schema,Schema.append]

theorem installed_computed : catalog GeneralDictionaryMixedCatalogReachable.installed = [closedRequest] := by
  change ([packet].reverse.flatMap packetRequests) = [closedRequest]
  simp [packet_computed]
end Yulang.GeneralDictionaryComputedCatalogExample
