import Yulang.GeneralDictionaryTerminalRefresh
import Yulang.GeneralDictionarySharedCurrentEvidence
import Yulang.GeneralNominalSharedPositive

/-! A genuinely informative constant-output terminal Shared installation and
actual observation refresh. It generates no consumer: this root-only fixture
does not establish consumer resumption. -/
namespace Yulang.GeneralDictionarySharedConstantRefresh
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport
open GeneralDictionaryRecursiveObstruction
open GeneralDictionaryCommittedEvidenceExamples (packet packet_children)
open GeneralDeclarationExamples (roles)
local instance : NeZero context.state.base.slots := ⟨by change 2 ≠ 0; omega⟩
abbrev start := GeneralNominalSupport.initial context root
local instance : NeZero start.current.context.state.base.slots := ⟨by change 2 ≠ 0; omega⟩
noncomputable def installed := GeneralNominalSharedSteps.install start packet []
noncomputable def refreshed : Tracked roles :=
  {installed with current := regenerate installed.current GeneralDictionaryTerminalRefresh.nextContext}

theorem source_ready_zero : ReadyAt start [] 0 := by
  exact source_ready start 0 (.nominal 0 1) _ _
    (Head.nominal (snapshot := context.state) 0 GeneralNominalExamples.listDescriptor rfl)
    (Head.nominal (snapshot := context.state) 0 GeneralNominalExamples.listDescriptor rfl) []

theorem decision : DecisionGuard start registry root [] := by
  refine ⟨(by intro _ impossible; cases impossible),(fun _ => source_ready_zero),?_⟩
  intro candidate visible _ bounds located slot member
  have equal := List.mem_singleton.mp visible
  subst candidate
  have same : bounds = [(0,0)] := Option.some.inj (located.symm.trans (by decide +kernel))
  subst bounds
  have reads : readsMany context.state
      (GeneralNominalInspection.queries context.state context.interpretation declaration) [(0,0)] = [0] := by
    rw [query_exact,readsMany.eq_def]
    dsimp only
    rw [GeneralNominalSupport.reads.eq_def]
    simp only [GeneralNominalExamples.state,GeneralNominalExamples.listDescriptor,
      GeneralNominalRecursiveInspection.typeArguments]
    simp only [List.mapM_cons,List.mapM_nil,ite_true]
    dsimp only [Bind.bind,Pure.pure,Option.bind]
    simp only [readsMany.eq_def]
    rw [GeneralNominalSupport.reads.eq_def]
    rfl
  change slot ∈ readsMany context.state (GeneralNominalInspection.queries context.state context.interpretation declaration) [(0,0)] at member
  rw [reads] at member
  have same := List.mem_singleton.mp member
  subst slot
  exact source_ready_zero

theorem old_guard : GeneralNominalSupportSteps.PacketGuard start packet [] :=
  ⟨⟨decision.1,decision.2.1,
    decision.2.2 declaration (by simp) rfl [(0,0)] (by decide +kernel)⟩,decision⟩

theorem guard : GeneralNominalSharedSteps.PacketGuard start packet [] := by
  exact GeneralNominalSharedSteps.leaf_guard rfl
    (GeneralNominalSharedPositive.leaf_input_coherent packet rfl)
    (GeneralNominalValueSupport.source_packet start packet old_guard)
    (GeneralNominalSharedPositive.initial_decision context root root registry [] decision)

theorem current_eq : installed.current = GeneralDictionaryJournalTreeExamples.after := by
  unfold installed GeneralNominalSharedSteps.install GeneralDictionaryJournalTreeExamples.after
    GeneralNominalFeedbackSites.install GeneralNominalSharedEmission.emitted GeneralNominalFeedbackSites.emitted
  simp only [packet_children,List.map_nil]
  rfl

theorem novel : ¬ GeneralNominalFeedbackSteps.Committed start.current packet := by
  intro committed
  exact bad_not_branch (committed.1 badModel ((initial_models context root _).mpr bad_original_model))

theorem install_step : GeneralNominalSharedSteps.Step registry root start installed :=
  ⟨root,.root,.install packet [] GeneralDictionaryJournalTreeExamples.enabled novel guard⟩

theorem refresh_step : GeneralNominalSharedSteps.Step registry root installed refreshed := by
  have certificate : GeneralNominalFeedbackSteps.Refresh installed.current GeneralDictionaryTerminalRefresh.nextContext := by
    rw [current_eq]
    exact GeneralDictionaryTerminalRefresh.certificate
  refine ⟨root,.root,.administrative root _ (.refresh root _ certificate 1 ?_ ?_ GeneralDictionaryTerminalRefresh.source_known)⟩
  · rw [current_eq]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_ofFn.mpr ⟨(1 : Fin 2),rfl⟩)))
  · rw [current_eq]
    exact GeneralDictionaryTerminalRefresh.source_unknown

theorem actual_prefix : B4Target.Steps (GeneralNominalSharedSteps.Step registry root) start refreshed :=
  .tail (.tail .refl install_step) refresh_step

theorem source_formed : GeneralNominalSharedSteps.SourceFormed registry root refreshed :=
  .update (.update (.initial context GeneralDictionaryJournalTreeFormation.initial_source) install_step) refresh_step

theorem refreshed_current : refreshed.current = GeneralDictionaryTerminalRefresh.refreshed := by
  change regenerate installed.current _ = _
  rw [current_eq]

theorem newly_known : ¬ GeneralNominalState.Known installed.current.context.state 1 ∧
    GeneralNominalState.Known refreshed.current.context.state 1 := by
  rw [current_eq,refreshed_current]
  exact ⟨GeneralDictionaryTerminalRefresh.source_unknown,GeneralDictionaryTerminalRefresh.source_known⟩

theorem inhabited : Models refreshed.current GeneralNominalExamples.model := by
  rw [refreshed_current]
  exact GeneralDictionaryTerminalRefresh.inhabited

theorem current_dictionary (model : GeneralNominalCommonBridge.Assignment)
    (valid : Models refreshed.current model) :
    GeneralDictionaryRecursiveEvidence.Evidence registry refreshed.current.context model root (.node 40 []) := by
  rw [refreshed_current] at valid ⊢
  exact GeneralDictionaryTerminalRefresh.current_evidence model valid

theorem generated_only_root (child : Occurrence roles)
    (generated : Generated refreshed.current root child) : child = root := by
  rw [refreshed_current] at generated
  exact GeneralDictionaryTerminalRefresh.generated_only_root child generated

theorem no_generated_consumer (child : Occurrence roles) (different : child ≠ root) :
    ¬ Generated refreshed.current root child := fun generated => different (generated_only_root child generated)

end Yulang.GeneralDictionarySharedConstantRefresh
