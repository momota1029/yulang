import Yulang.GeneralDictionaryTerminalRefresh
import Yulang.GeneralNominalSupportBoundary

/-! A genuine nonempty support journal reaches a stable, modeled terminal
completion. Current evidence is independently checked after scalar refresh. -/
namespace Yulang.GeneralDictionarySupportNonemptyExample
open GeneralDictionaryRecursiveObstruction GeneralNominalSaturationState GeneralNominalSupport
open GeneralDeclarations GeneralSourceDictionaries
open GeneralDictionaryCommittedEvidenceExamples (packet)
open GeneralDeclarationExamples (roles)

abbrev start : Tracked roles := GeneralNominalSupport.initial context root
noncomputable abbrev installed := GeneralNominalSupportSteps.install start packet []
noncomputable abbrev finish : Tracked roles :=
  { installed with current := GeneralDictionaryTerminalRefresh.refreshed }

private theorem root_ready : Roots start [] root := by
  intro index
  exact source_ready start 0 (.nominal 0 1) _ _
    (Head.nominal (snapshot := context.state) (0 : Fin 2) GeneralNominalExamples.listDescriptor rfl)
    (Head.nominal (snapshot := context.state) (0 : Fin 2) GeneralNominalExamples.listDescriptor rfl) []

theorem decisions : DecisionGuard start registry root [] := by
  refine ⟨(by intro _ impossible; cases impossible),root_ready,?_⟩
  intro decl member role bounds located slot inspected
  have same := List.mem_singleton.mp member
  subst decl
  have actual : bounds = [(⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩)] :=
    Option.some.inj (located.symm.trans (by rfl))
  subst bounds
  have read_exact : readsMany context.state
      (GeneralNominalInspection.queries context.state context.interpretation declaration) [(0,0)] = [(0 : Fin 2)] := by
    rw [query_exact]
    simp [readsMany,GeneralNominalSupport.reads,context,GeneralNominalExamples.context,
      GeneralNominalExamples.state,GeneralNominalExamples.listDescriptor,GeneralNominalRecursiveInspection.typeArguments]
    change readsMany context.state [.variables [0]] [(1,1)] = []
    simp [readsMany,GeneralNominalSupport.reads]
  change slot ∈ readsMany context.state
      (GeneralNominalInspection.queries context.state context.interpretation declaration) [(0,0)] at inspected
  rw [read_exact] at inspected
  have zero : slot = (0 : Fin 2) := List.mem_singleton.mp inspected
  subst slot
  exact source_ready start 0 (.nominal 0 1) _ _
    (Head.nominal (snapshot := context.state) (0 : Fin 2) GeneralNominalExamples.listDescriptor rfl)
    (Head.nominal (snapshot := context.state) (0 : Fin 2) GeneralNominalExamples.listDescriptor rfl) []

theorem packet_guard : GeneralNominalSupportSteps.PacketGuard start packet [] :=
  ⟨⟨decisions.1,decisions.2.1,decisions.2.2 declaration (List.mem_singleton_self _) rfl _ rfl⟩,decisions⟩

theorem install_step : GeneralNominalSupportSteps.Step registry root start installed := by
  refine ⟨root,.root,.install packet [] GeneralDictionaryJournalTreeExamples.enabled ?_ packet_guard⟩
  intro committed
  exact bad_not_branch (committed.1 badModel ((initial_models context root _).mpr bad_original_model))

theorem refresh_step : GeneralNominalSupportSteps.Step registry root installed finish := by
  refine ⟨root,.root,.administrative root _ (.refresh root GeneralDictionaryTerminalRefresh.nextContext
    GeneralDictionaryTerminalRefresh.certificate 1 ?_ GeneralDictionaryTerminalRefresh.source_unknown
    GeneralDictionaryTerminalRefresh.source_known)⟩
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨(1 : Fin 2),rfl⟩)))

theorem actual_path : B4Target.Steps (GeneralNominalSupportSteps.Step registry root) start finish :=
  .tail (.tail .refl install_step) refresh_step

theorem reachable : B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry root finish :=
  ⟨start,⟨context,GeneralDictionaryJournalTreeFormation.initial_source,rfl⟩,actual_path⟩

theorem point_closed : GeneralNominalReobservationSteps.PointClosed GeneralDictionaryTerminalRefresh.nextState := by
  intro slot descriptor recorded parameter member
  change Fin 2 at slot
  change (if slot = (0 : Fin 2) then some GeneralNominalExamples.listDescriptor else none) = some descriptor at recorded
  by_cases zero : slot = (0 : Fin 2)
  · subst slot
    have same := Option.some.inj recorded
    subst descriptor
    have same := List.mem_singleton.mp member
    subst parameter
    rfl
  · simp [zero] at recorded

theorem stable : GeneralNominalSupportSteps.Stable registry finish root := by
  have old := GeneralNominalReobservationSteps.stable_of_pointClosed GeneralDictionaryTerminalRefresh.stable point_closed
  intro focus generated next update
  exact old focus generated next.current (GeneralNominalSupportSteps.at_old update)

theorem nonempty : finish.current.packets ≠ [] := by
  intro impossible
  cases impossible

theorem inhabited : Models finish.current GeneralNominalExamples.model := GeneralDictionaryTerminalRefresh.inhabited

theorem current_instance (model : GeneralNominalCommonBridge.Assignment) (valid : Models finish.current model) :
    GeneralDictionaryRecursiveEvidence.Instance registry finish.current.context model root 40 [] :=
  GeneralDictionaryTerminalRefresh.current_instance model valid

theorem current_evidence (model : GeneralNominalCommonBridge.Assignment) (valid : Models finish.current model) :
    GeneralDictionaryRecursiveEvidence.Evidence registry finish.current.context model root (.node 40 []) :=
  GeneralDictionaryTerminalRefresh.current_evidence model valid

theorem completed :
    B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry root finish ∧
    GeneralNominalSupportSteps.Stable registry finish root ∧ finish.current.packets ≠ [] ∧
    Models finish.current GeneralNominalExamples.model ∧
    ∀ model, Models finish.current model →
      GeneralDictionaryRecursiveEvidence.Evidence registry finish.current.context model root (.node 40 []) :=
  ⟨reachable,stable,nonempty,inhabited,current_evidence⟩
end Yulang.GeneralDictionarySupportNonemptyExample
