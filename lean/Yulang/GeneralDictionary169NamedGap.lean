import Yulang.GeneralDictionary169SharedStable
import Yulang.GeneralDictionaryMixed168Tree

/-! Empty-journal named-output requests lie outside the old MixedTree syntax.
The actual source-formed, Shared-stable example has a semantic dictionary, so
this is a certificate coverage gap, not inconsistency of the target language. -/
namespace Yulang.GeneralDictionary169NamedGap
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport
open GeneralDictionaryMixed168Tree (MixedTree)
variable {roles : Roles.RoleDecls}

theorem empty_named_not_mixed {registry : Registry} {state : Tracked roles}
    {occurrence : Occurrence roles} (empty : state.current.packets = [])
    (named : occurrence.demand.outputs ≠ []) (payload : GeneralDictionaryReadback.Payload) :
    ¬ MixedTree registry state occurrence payload := by
  intro tree
  cases tree with
  | recorded packet member relocation payloads children =>
    rw [empty] at member
    cases member
  | scalar occurrence declaration visible checked shape => exact named shape.outputs
  | spine occurrence declaration visible checked shape => exact named shape.outputs

open GeneralDictionaryFiniteObservedExample

theorem actual_not_mixed (payload : GeneralDictionaryReadback.Payload) :
    ¬ MixedTree registry start root payload :=
  empty_named_not_mixed rfl named_request_present payload

/-- One inhabited Shared-stable source has named-output semantic evidence but
no old mixed certificate at any payload. No V5 bridge is refuted here. -/
theorem stable_named_coverage_gap :
    GeneralNominalSharedSteps.SourceFormed registry root start ∧
    GeneralNominalSharedSteps.Stable registry start root ∧
    Models start.current model ∧
    GeneralDictionaryRecursiveEvidence.Evidence registry start.current.context model root
      (.node declaration.id []) ∧
    ∀ payload, ¬ MixedTree registry start root payload := by
  obtain ⟨formed,stable,valid,_named,evidence⟩ := GeneralDictionary169SharedStable.actual_stable_named_dictionary
  exact ⟨formed,stable,valid,evidence model valid,actual_not_mixed⟩
end Yulang.GeneralDictionary169NamedGap
