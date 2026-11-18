import Yulang.GeneralRebaseNamedRequest260
namespace Cycle260DecoderScopeProbe
open Yulang
open GeneralDictionaryDefaultGap206Source

-- The checked runner computes constraints. Its successful return alone does
-- not certify the particular caller assignment as a satisfying model.
theorem successful_run_is_not_assignment_validation :
 GeneralDefaultRebaseModels260.Models GeneralDefaultRebaseSource260.initialState counter ∧
 GeneralDefaultRebaseRun260.run GeneralDefaultRebaseSource260.initialState =
   .ok (some GeneralDefaultRebaseSource260.finalState) ∧
 ¬ GeneralDefaultRebaseModels260.Models GeneralDefaultRebaseSource260.finalState counter :=
 ⟨GeneralDefaultRebaseInstalled260.counter_removed.1,GeneralDefaultRebaseRun260.first,
  GeneralDefaultRebaseInstalled260.counter_removed.2⟩

-- Missing declarations remain explicit errors, including through the new
-- named-request wrapper. Name999 is an internal test argument, not a source
-- rejection diagnosis or a claim that this request is reachable.
theorem missing_body : GeneralRebaseBodyDecoder260.compile plan 37 ⟨999,0⟩ = .error .missingBody := rfl

theorem named_missing_body : GeneralRebaseNamedRequest260.compile plan 37 2 ⟨999,0⟩ = .error .missingBody := rfl

-- The namespaced address space is internally injective but is not disjoint
-- from every old owner-only table. A migration must replace or separately tag
-- the old table, rather than mix both encodings without a further argument.
theorem old_namespace_overlap : GeneralRebaseRequestBodyKeys260.key 0 0 0 0 =
 GeneralRebaseOwnedOutputKeys260.key 0 0 := rfl

#print axioms successful_run_is_not_assignment_validation
#print axioms missing_body
#print axioms named_missing_body
#print axioms old_namespace_overlap
end Cycle260DecoderScopeProbe
