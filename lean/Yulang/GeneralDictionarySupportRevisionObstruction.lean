import Yulang.GeneralDictionaryCurrentRevisionObstruction
import Yulang.GeneralDictionarySupportJournal

/-! The literal-current obstruction survives the actual provenance guards.
This is an initial, source-supported installation followed by certified point
replacement. It does not assert stability or refute V5 Evidence. -/
namespace Yulang.GeneralDictionarySupportRevisionObstruction
open GeneralNominalFeedbackObstruction GeneralNominalSaturationState
open GeneralNominalSupport GeneralSourceDictionaries GeneralDeclarations
open GeneralDeclarationExamples (roles)

abbrev start : Tracked roles := GeneralNominalSupport.initial context root
noncomputable abbrev trackedInstalled := GeneralNominalSupportSteps.install start packet []
noncomputable abbrev finish : Tracked roles :=
  { trackedInstalled with current := GeneralDictionaryCurrentRevisionObstruction.revised }

private theorem root_ready : Roots start [] root := by
  intro index
  change ReadyAt start [] 0
  exact source_ready start 0 (.nominal 0 1) _ _
    (Head.nominal (snapshot := source) (0 : Fin 4) GeneralNominalIntervalExamples.descriptor rfl)
    (Head.nominal (snapshot := source) (0 : Fin 4) GeneralNominalIntervalExamples.descriptor rfl) []

theorem decisions : DecisionGuard start registry root [] := by
  refine ⟨(by intro _ impossible; cases impossible),root_ready,?_⟩
  intro decl member role bounds located slot read
  have same := List.mem_singleton.mp member
  subst decl
  have actual : bounds = [(⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩)] :=
    Option.some.inj (located.symm.trans (by rfl))
  subst bounds
  have readZero : slot = (0 : Fin 4) := by
    have reads : readsMany start.current.context.state
        (GeneralNominalInspection.queries start.current.context.state start.current.context.interpretation declaration)
        [(⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩)] = [(⟨0,by decide +kernel⟩ : Fin 4)] := by
      have query : GeneralNominalInspection.queries source context.interpretation declaration =
          [.nominal 0 [.variables [0]]] := by
        simp [GeneralNominalInspection.queries,Declaration.normalHead,
          GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
          GeneralNominalInspection.translate,GeneralNominalExamples.interpretation]
      change readsMany source (GeneralNominalInspection.queries source context.interpretation declaration) [(0,0)] = [0]
      rw [query]
      simp [readsMany,GeneralNominalSupport.reads,source,
        GeneralNominalIntervalExamples.source,GeneralNominalIntervalExamples.descriptor,
        GeneralNominalRecursiveInspection.typeArguments]
      change readsMany source [.variables [0]] [(2,3)] = []
      simp [readsMany,GeneralNominalSupport.reads]
    rw [reads] at read
    exact List.mem_singleton.mp read
  subst slot
  exact source_ready start 0 (.nominal 0 1) _ _
    (Head.nominal (snapshot := source) (0 : Fin 4) GeneralNominalIntervalExamples.descriptor rfl)
    (Head.nominal (snapshot := source) (0 : Fin 4) GeneralNominalIntervalExamples.descriptor rfl) []

theorem packet_guard : GeneralNominalSupportSteps.PacketGuard start packet [] :=
  ⟨⟨decisions.1,decisions.2.1,decisions.2.2 declaration (List.mem_singleton_self _) rfl _ rfl⟩,decisions⟩

theorem installation : GeneralNominalSupportSteps.Step registry root start trackedInstalled := by
  refine ⟨root,.root,.install packet [] GeneralNominalFeedbackRegressions.enabled ?_ packet_guard⟩
  intro committed
  have absent := committed.2 child (by rw [children_exact]; simp)
  cases absent

theorem revision_step : GeneralNominalSupportSteps.Step registry root trackedInstalled finish :=
  ⟨root,.root,.administrative root _ (.reobserve root
    GeneralDictionaryCurrentRevisionObstruction.revision
    GeneralDictionaryCurrentRevisionObstruction.certified
    GeneralDictionaryCurrentRevisionObstruction.improves)⟩

theorem actual_path : B4Target.Steps (GeneralNominalSupportSteps.Step registry root) start finish :=
  .tail (.tail .refl installation) revision_step

theorem reachable : B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry root finish :=
  ⟨start,⟨context,initial_source,rfl⟩,actual_path⟩

theorem modeled_nonempty : Models finish.current model ∧ finish.current.packets ≠ [] :=
  GeneralDictionaryCurrentRevisionObstruction.modeled_nonempty

theorem not_current : ¬ GeneralDictionaryCurrentJournal.Current registry finish.current :=
  GeneralDictionaryCurrentRevisionObstruction.not_current

/-- A source-supported actual path, not a raw fabricated journal. -/
theorem reachable_current_failure :
    (GeneralNominalSupportBoundary.boundary roles).Initial registry root start ∧
    B4Target.Steps (GeneralNominalSupportSteps.Step registry root) start finish ∧
    Models finish.current model ∧ finish.current.packets ≠ [] ∧
    ¬ GeneralDictionaryCurrentJournal.Current registry finish.current :=
  ⟨⟨context,initial_source,rfl⟩,actual_path,modeled_nonempty.1,modeled_nonempty.2,not_current⟩

/-- Historical soundness and literal-current failure coexist in one modeled,
reachable state. The distinction is semantic, not a missing model. -/
theorem historical_but_not_current :
    (∀ valuation, Models finish.current valuation →
      GeneralDictionaryRecursiveEvidence.Instance registry packet.context valuation
        packet.site.occurrence packet.declaration.id packet.children) ∧
    ¬ GeneralDictionaryCurrentJournal.Current registry finish.current := by
  refine ⟨?_,not_current⟩
  have formed := GeneralNominalSupportBoundary.reachable_formed registry finish root reachable
  have recorded : packet ∈ finish.current.packets := by exact List.mem_singleton_self _
  have historical := (GeneralDictionarySupportJournal.recorded_instances
    registry root finish formed packet recorded).1
  exact historical

end Yulang.GeneralDictionarySupportRevisionObstruction
