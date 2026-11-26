import Yulang.GeneralDeclarativeI65I75ProjectedRule426
import «Cycle428I74StructuralWhereBodyReplay»

set_option maxRecDepth 3000
namespace Yulang.GeneralDeclarativeI65.I72.StructuralWhereIntegratedLegacy428
open StructuralWhere428 StructuralWhereMixedSibling428 StructuralWhereBodyReplay428

def actualSibling : Checker408.Problem := ⟨mixedProblem.state,reconstructed.second.actual.child⟩
def report : Checker408.Result := Check408.nullaryReport reconstructed.namedDecl
def currentWitness : EndpointProjection426.Witness :=
  .previous (existingBareNameRoute428 reconstructed.legacyWire)

/-- Checks the unchanged current integrated public R14 entry on the
actual independently reconstructed *legacy sibling*. No public
dispatch for its C15 parent is added or assumed. -/
theorem actual_legacy_sibling_passes_current_integrated_R14_entry428 :
    EndpointProjection426.check actualSibling report currentWitness = true := by decide +kernel

theorem current_integrated_R14_uses_the_same_legacy_child_request428 :
    Classifies EndpointProjection426.R14 mixedProblem.state reconstructed.second.actual.child report.verdict :=
  (EndpointProjection426.verified_R14_result_classifies_in_same_State426 actualSibling report currentWitness
    actual_legacy_sibling_passes_current_integrated_R14_entry428).1

#print axioms actual_legacy_sibling_passes_current_integrated_R14_entry428
#print axioms current_integrated_R14_uses_the_same_legacy_child_request428

end Yulang.GeneralDeclarativeI65.I72.StructuralWhereIntegratedLegacy428
