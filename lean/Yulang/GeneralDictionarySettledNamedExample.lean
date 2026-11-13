import Yulang.GeneralDictionarySettledRecursiveExample
import Yulang.GeneralDictionaryFiniteObservedExampleNonterminalClassification

/-! A nonempty named-output producer under I26. Its actual output target is
already source-observed, so this is NOT a blocked-consumer counterexample. -/
namespace Yulang.GeneralDictionarySettledNamedExample
open GeneralDictionaryFiniteObservedExampleNonterminal
open GeneralDictionaryFiniteObservedExampleNonterminalInstallation
open GeneralDictionaryFiniteObservedExampleNonterminalEvidence
open GeneralDictionaryFiniteObservedExampleNonterminalFinalEvidence
open GeneralDictionaryFiniteObservedExampleNonterminalClassification
open GeneralDictionaryFiniteObservedExample (model descriptor)
open GeneralDeclarationExamples (roles)
open GeneralNominalSaturationState GeneralSourceDictionaries
open GeneralNominalSupport (Head)

private theorem heads (slot : Fin 2) :
    ∃ test observation currentObservation, Head source slot.val test observation ∧
      Head installed.current.context.state slot.val test currentObservation := by
  by_cases zero : slot.val = 0
  · have same : slot = 0 := Fin.ext zero
    subst slot
    exact ⟨_,_,_,Head.nominal (snapshot := source) (0 : Fin 2) descriptor rfl,
      Head.nominal (snapshot := installed.current.context.state) (0 : Fin 2) descriptor rfl⟩
  · have same : slot = (1 : Fin 2) := by apply Fin.ext; omega
    subst slot
    exact ⟨_,_,_,Head.scalar (snapshot := source) (1 : Fin 2) .int rfl,
      Head.scalar (snapshot := installed.current.context.state) (1 : Fin 2) .int rfl⟩

theorem initial_decision : GeneralNominalSettledSupport.DecisionGuard registry start root := by
  constructor
  · intro index
    obtain ⟨test,observation,_,head,_⟩ := heads 0
    exact ⟨test,observation,head,GeneralNominalSettledSupport.source_head start head⟩
  · intro declaration visible role bounds located slot member
    obtain ⟨test,observation,_,head,_⟩ := heads slot
    exact ⟨test,observation,head,GeneralNominalSettledSupport.source_head start head⟩

theorem install_guard : GeneralNominalSettledSupport.PacketGuard start packet [] :=
  ⟨GeneralNominalValueSupport.source_packet start packet guard,initial_decision⟩

theorem actual_step : GeneralNominalSettledSteps.Step registry root start installed :=
  ⟨root,.root,.install packet [] enabled novel install_guard⟩

theorem reachable : B4TargetV5.Reachable (GeneralNominalSettledBoundary.boundary roles)
    registry root installed := ⟨start,⟨context,initial_source,rfl⟩,.tail .refl actual_step⟩

theorem stable : GeneralNominalSettledSteps.Stable registry installed root := by
  intro focus reached next update
  exact value_stable focus reached next (GeneralNominalSettledSteps.at_old update)

theorem current_decision (focus : Occurrence roles) (slot : Fin 2)
    (args : ∀ index, focus.demand.arguments index = (slot.val,slot.val)) :
    GeneralNominalSettledSupport.DecisionGuard registry installed focus := by
  constructor
  · intro index
    rw [show (focus.demand.arguments index).1 = slot.val by rw [args index]]
    obtain ⟨test,observation,currentObservation,head,seen⟩ := heads slot
    exact ⟨test,currentObservation,seen,GeneralNominalSettledSupport.source_head installed head⟩
  · intro declaration visible role bounds located read member
    obtain ⟨test,observation,currentObservation,head,seen⟩ := heads read
    exact ⟨test,currentObservation,seen,GeneralNominalSettledSupport.source_head installed head⟩

private theorem selected {key : Nat} {children : List (Occurrence roles)} (focus : Occurrence roles) (slot : Fin 2)
    (args : ∀ index, focus.demand.arguments index = (slot.val,slot.val))
    (old : GeneralNominalValueBoundary.Local registry installed focus (.selected key children)) :
    GeneralNominalSettledBoundary.Local registry installed focus (.selected key children) := by
  cases old with
  | selected safe unique =>
    refine .selected ⟨safe.1,safe.2.1,safe.2.2.1,?_⟩ unique
    rintro (blocked | blocked)
    · exact safe.2.2.2 blocked
    · exact blocked (current_decision focus slot args)

theorem parent_selected : GeneralNominalSettledBoundary.Local registry installed root
    (.selected declaration.id children) := selected root 0 (fun _ => rfl) value_parent

theorem child_selected : GeneralNominalSettledBoundary.Local registry installed child
    (.selected GeneralNominalExamples.intDisplay.id []) := selected child 1 (by
      intro index
      have bound : index.val < 1 := index.isLt
      have zero : index = ⟨0,by change 0 < 1; decide⟩ := by apply Fin.ext; change index.val = 0; omega
      subst index
      decide +kernel) value_child

theorem classified : B4TargetV3.Classify (GeneralNominalSettledBoundary.boundary roles).toSourceBoundary
    registry installed root (.selected payload) := by
  have parent := (GeneralNominalSettledBoundary.local_correspondence registry installed root _).mpr parent_selected
  rw [children_exact] at parent
  have leaf := (GeneralNominalSettledBoundary.local_correspondence registry installed child _).mpr child_selected
  cases parent with
  | selected safe unique =>
    apply B4TargetV3.Classify.selected safe unique
    cases leaf with
    | selected childSafe childUnique => exact .cons (.selected childSafe childUnique .nil) .nil

theorem completed_named :
    GeneralNominalSettledSteps.Step registry root start installed ∧
    B4TargetV5.Reachable (GeneralNominalSettledBoundary.boundary roles) registry root installed ∧
    GeneralNominalSettledSteps.Stable registry installed root ∧
    Models installed.current model ∧ root.demand.outputs ≠ [] ∧
    B4TargetV3.Classify (GeneralNominalSettledBoundary.boundary roles).toSourceBoundary
      registry installed root (.selected payload) ∧
    ∀ assignment, Models installed.current assignment →
      GeneralDictionaryRecursiveEvidence.Evidence registry installed.current.context assignment root payload :=
  ⟨actual_step,reachable,stable,models_of_source model source_models,named_request_present,classified,final_evidence⟩

theorem no_discharged (focus : Occurrence roles) : ¬ GeneralNominalSupport.Discharged installed.current focus := by
  apply GeneralDictionarySettledRecursiveExample.no_discharge_without_terminal_packet installed.current
  intro recorded member
  have same : recorded = packet := List.mem_singleton.mp member
  subst recorded
  exact children_nonempty

theorem named_packet_unsettled : GeneralNominalSettledSupport.Unsettled installed.current packet :=
  ⟨List.mem_singleton_self packet,child,by change child ∈ children; rw [children_exact]; simp,no_discharged child⟩

/-- Its output origin has a source explanation despite the packet's unsettled
ledger. Therefore this example does not demonstrate wrongful blocking. -/
theorem output_head_independent : GeneralNominalSettledSupport.HeadJustified installed 0
    (.nominal descriptor.declaration.name descriptor.arguments.length) :=
  GeneralNominalSettledSupport.source_head installed (Head.nominal (snapshot := source) (0 : Fin 2) descriptor rfl)

end Yulang.GeneralDictionarySettledNamedExample
