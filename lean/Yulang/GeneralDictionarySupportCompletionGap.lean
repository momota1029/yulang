import Yulang.GeneralDictionarySupportEvidence
import Yulang.GeneralDictionaryReachableEvidenceProvenance

/-! A genuine source-supported installation still need not make every raw
context model a journal model. This excludes a shortcut to removing Joint;
it is not a stable-selected counterexample, nor a refutation of V5 Evidence. -/
namespace Yulang.GeneralDictionarySupportCompletionGap
open GeneralNominalFeedbackObstruction GeneralNominalSaturationState
open GeneralNominalSupport

abbrev start := GeneralNominalSupport.initial context root

private theorem inspected :
    readsMany source (GeneralNominalInspection.queries source context.interpretation declaration)
      [(0,0)] = [(0 : Fin 4)] := by
  decide +kernel

theorem source_decision : DecisionGuard start registry root [] := by
  have ready : ReadyAt start [] 0 := source_ready start 0 (.nominal 0 1) _ _
    (Head.nominal (snapshot := source) 0 GeneralNominalIntervalExamples.descriptor rfl)
    (Head.nominal (snapshot := source) 0 GeneralNominalIntervalExamples.descriptor rfl) []
  refine ⟨(by intro _ impossible; cases impossible),fun _ => ready,?_⟩
  intro decl member role bounds located slot read
  have same := List.mem_singleton.mp member
  subst decl
  have eq := Option.some.inj located
  subst bounds
  change slot ∈ readsMany source (GeneralNominalInspection.queries source context.interpretation declaration)
      [(0,0)] at read
  rw [inspected] at read
  have same := List.mem_singleton.mp read
  subst slot
  exact ready

theorem packet_guard : GeneralNominalSupportSteps.PacketGuard start packet [] :=
  ⟨⟨source_decision.1,source_decision.2.1,
    source_decision.2.2 declaration (List.mem_singleton_self _) rfl _ rfl⟩,source_decision⟩

noncomputable abbrev finish := GeneralNominalSupportSteps.install start packet []

theorem actual_step : GeneralNominalSupportSteps.Step registry root start finish := by
  refine ⟨root,.root,.install packet [] GeneralNominalFeedbackRegressions.enabled ?_ packet_guard⟩
  intro committed
  have absent := committed.2 child (by rw [children_exact]; simp)
  cases absent

theorem actual_reachable : B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary GeneralDeclarationExamples.roles)
    registry root finish :=
  ⟨start,⟨context,initial_source,rfl⟩,.tail .refl actual_step⟩

theorem actual_inhabited : Models finish.current model := installed_models

theorem actual_nonempty : finish.current.packets ≠ [] := by
  change packet :: initialState.packets ≠ []
  simp

theorem context_incomplete : ¬ ContextComplete finish.current :=
  GeneralDictionaryReachableEvidenceProvenance.formed_inhabited_context_incomplete.2.2

/-- The witness is an actual support trace, not a fabricated ledger. Stability
and selectedness at the resulting state are intentionally not asserted. -/
theorem no_reachable_context_complete :
    ¬ (∀ state : Tracked GeneralDeclarationExamples.roles,
      B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary GeneralDeclarationExamples.roles)
        registry root state → (∃ model, Models state.current model) → ContextComplete state.current) := by
  intro shortcut
  exact context_incomplete (shortcut finish actual_reachable ⟨model,actual_inhabited⟩)

end Yulang.GeneralDictionarySupportCompletionGap
