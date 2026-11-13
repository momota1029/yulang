import Yulang.GeneralDictionaryNestedRefinementReplay
import Yulang.GeneralNominalProvenanceSource

/-! A positive two-level nominal query on a genuinely nonpoint outer interval.
The two arms retain separate source identities and one repeated capture name.
The target refinement below is arbitrary, not assumed to have an equal report. -/
namespace Yulang.GeneralDictionaryNestedRefinementExamples
open GeneralDictionaryNestedRefinement
open GeneralNominalRecursiveInspection
open GeneralNominalProvenanceSource
abbrev query : GeneralNominalInspection.Query := .nominal 0 [.nominal 0 [.variables [7]]]
abbrev bounds : GeneralNominalInspection.Bounds state := (0,3)

theorem nested_scope : NominalOnly query := by trivial

theorem nested_finished : Finished (inspect state query bounds none) := by
 unfold Finished
 decide +kernel

theorem captures_two_sources : bindings state (inspect state query bounds none) = [(7,2,2),(7,5,5)] := by
 decide +kernel

theorem positive_nonpoint : (bounds.1 ≠ bounds.2) ∧
 GeneralNominalState.Models state (model .bottom .top .bottom) ∧
 Finished (inspect state query bounds none) :=
 ⟨by decide +kernel,source_models _ _ _,nested_finished⟩

theorem arbitrary_refinement (after : GeneralNominalState.State)
 (r : GeneralNominalRefinements.Refines state after) :
 inspect after query (mapBounds r.base.embed bounds) none =
 mapReport r.base.embed (inspect state query bounds none) :=
 inspect_refined state after r query bounds none nested_scope nested_finished

end Yulang.GeneralDictionaryNestedRefinementExamples
