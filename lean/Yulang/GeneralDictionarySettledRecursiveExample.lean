import Yulang.GeneralNominalSettledBoundary
import Yulang.GeneralDictionarySupportRecursiveClosure

/-! A source-supported recursive success under the actual I26 relation.
The old stronger stability theorem is restricted to the guarded relation;
new stability is never used to infer old stability. -/
namespace Yulang.GeneralDictionarySettledRecursiveExample
open GeneralDictionarySupportRecursiveExample GeneralDictionarySupportRecursiveClassification
open GeneralNominalExamples GeneralNominalSaturationState GeneralSourceDictionaries
open GeneralDeclarationExamples (roles)
open GeneralNominalSupport (Head)

private theorem source_heads (slot : Fin 2) :
    ∃ test observation, Head (state true) slot.val test observation := by
  by_cases zero : slot.val = 0
  · have same : slot = 0 := Fin.ext zero
    subst slot
    exact ⟨_,_,.nominal 0 listDescriptor rfl⟩
  · have same : slot = (1 : Fin 2) := by apply Fin.ext; omega
    subst slot
    exact ⟨_,_,.scalar 1 .int rfl⟩

private theorem initial_ready (slot : Fin 2) :
    GeneralNominalSettledSupport.ReadyAt start slot.val := by
  obtain ⟨test,observation,head⟩ := source_heads slot
  exact ⟨test,observation,head,GeneralNominalSettledSupport.source_head start head⟩

theorem initial_decision :
    GeneralNominalSettledSupport.DecisionGuard registry start displayRoot := by
  constructor
  · intro index
    exact initial_ready 0
  · intro declaration visible role bounds located slot member
    exact initial_ready slot

theorem install_guard : GeneralNominalSettledSupport.PacketGuard start packet [] := by
  refine ⟨GeneralNominalValueSupport.source_packet start packet ?_,?_⟩
  · exact GeneralNominalSupportExamples.display_guard
  · exact initial_decision

theorem actual_step : GeneralNominalSettledSteps.Step registry displayRoot start finish := by
  refine ⟨displayRoot,.root,.install packet [] enabled ?_ install_guard⟩
  intro committed
  have missing := committed.2 displayChild (by rw [children_exact]; simp)
  cases missing

theorem reachable : B4TargetV5.Reachable (GeneralNominalSettledBoundary.boundary roles)
    registry displayRoot finish :=
  ⟨start,⟨context true,initial_source,rfl⟩,.tail .refl actual_step⟩

theorem stable : GeneralNominalSettledSteps.Stable registry finish displayRoot := by
  intro focus generated after update
  apply GeneralDictionarySupportRecursiveClosure.stable focus generated after
  exact GeneralNominalDownstreamSteps.at_old
    (GeneralNominalValueSteps.at_old (GeneralNominalSettledSteps.at_old update))

private theorem current_heads (slot : Fin 2) :
    ∃ test observation currentObservation, Head (state true) slot.val test observation ∧
      Head finish.current.context.state slot.val test currentObservation := by
  by_cases zero : slot.val = 0
  · have same : slot = 0 := Fin.ext zero
    subst slot
    exact ⟨_,_,_,Head.nominal (snapshot := state true) (0 : Fin 2) listDescriptor rfl,Head.nominal (snapshot := finish.current.context.state) (0 : Fin 2) listDescriptor rfl⟩
  · have same : slot = (1 : Fin 2) := by apply Fin.ext; omega
    subst slot
    exact ⟨_,_,_,Head.scalar (snapshot := state true) (1 : Fin 2) .int rfl,Head.scalar (snapshot := finish.current.context.state) (1 : Fin 2) .int rfl⟩

private theorem current_ready (slot : Fin 2) :
    GeneralNominalSettledSupport.ReadyAt finish slot.val := by
  obtain ⟨test,observation,currentObservation,head,seen⟩ := current_heads slot
  exact ⟨test,currentObservation,seen,GeneralNominalSettledSupport.source_head finish head⟩

theorem current_decision (root : Occurrence roles) (slot : Fin 2)
    (args : ∀ index, root.demand.arguments index = (slot.val,slot.val)) :
    GeneralNominalSettledSupport.DecisionGuard registry finish root := by
  constructor
  · intro index
    rw [show (root.demand.arguments index).1 = slot.val by rw [args index]]
    exact current_ready slot
  · intro declaration visible role bounds located read member
    exact current_ready read

private theorem current_old_decision (root : Occurrence roles) (slot : Fin 2)
    (args : ∀ index, root.demand.arguments index = (slot.val,slot.val)) :
    GeneralNominalSupport.DecisionGuard finish registry root [] := by
  refine ⟨(by intro _ h; cases h),?_,?_⟩
  · intro index
    rw [show (root.demand.arguments index).1 = slot.val by rw [args index]]
    obtain ⟨test,observation,currentObservation,source,seen⟩ := current_heads slot
    exact GeneralNominalSupport.source_ready finish slot.val test observation currentObservation source seen []
  · intro declaration visible role bounds located read member
    obtain ⟨test,observation,currentObservation,source,seen⟩ := current_heads read
    exact GeneralNominalSupport.source_ready finish read.val test observation currentObservation source seen []

private theorem selected (root : Occurrence roles) (slot : Fin 2)
    (args : ∀ index, root.demand.arguments index = (slot.val,slot.val))
    (old : GeneralNominalSupportBoundary.Local registry finish root (.selected key children)) :
    GeneralNominalSettledBoundary.Local registry finish root (.selected key children) := by
  have value := GeneralNominalValueBoundary.selected_supported
    (GeneralNominalSupportBoundary.selected_old old) []
    (GeneralNominalValueSupport.source_decision registry finish root (current_old_decision root slot args))
  cases value with
  | selected safe unique =>
    refine .selected ⟨safe.1,safe.2.1,safe.2.2.1,?_⟩ unique
    rintro (blocked | blocked)
    · exact safe.2.2.2 blocked
    · exact blocked (current_decision root slot args)

theorem parent_selected : GeneralNominalSettledBoundary.Local registry finish displayRoot
    (.selected 1 [displayChild]) := selected displayRoot 0 (fun _ => rfl) supported_parent_selected

theorem leaf_selected : GeneralNominalSettledBoundary.Local registry finish displayChild
    (.selected 3 []) := selected displayChild 1 (fun _ => rfl) supported_leaf_selected

theorem classified : B4TargetV3.Classify (GeneralNominalSettledBoundary.boundary roles).toSourceBoundary
    registry finish displayRoot (.selected (.node 1 [.node 3 []])) := by
  have parent := (GeneralNominalSettledBoundary.local_correspondence registry finish displayRoot _).mpr parent_selected
  have leaf := (GeneralNominalSettledBoundary.local_correspondence registry finish displayChild _).mpr leaf_selected
  cases parent with
  | selected safe unique =>
    apply B4TargetV3.Classify.selected safe unique
    cases leaf with
    | selected childSafe childUnique => exact .cons (.selected childSafe childUnique .nil) .nil

/-- A real recursive installation is permitted by I26 source explanations,
reaches a stable classified state, and has the selected dictionary in EVERY
final model. This concrete result is not the general V5 evidenceNode. -/
theorem completed :
    B4TargetV5.Reachable (GeneralNominalSettledBoundary.boundary roles) registry displayRoot finish ∧
    GeneralNominalSettledSteps.Stable registry finish displayRoot ∧
    finish.current.packets ≠ [] ∧ Models finish.current model ∧
    B4TargetV3.Classify (GeneralNominalSettledBoundary.boundary roles).toSourceBoundary
      registry finish displayRoot (.selected (.node 1 [.node 3 []])) ∧
    ∀ assignment, Models finish.current assignment →
      GeneralDictionaryRecursiveEvidence.Evidence registry finish.current.context assignment
        displayRoot (.node 1 [.node 3 []]) :=
  ⟨reachable,stable,nonempty_journal,current_model,classified,final_recursive_evidence⟩

/-- No terminal recorded packet means that the inductive discharge relation
has no base case. This is independent of selection and semantic Evidence. -/
theorem no_discharge_without_terminal_packet {r : Roles.RoleDecls} (journal : State r)
    (nonterminal : ∀ recorded ∈ journal.packets, recorded.children ≠ [])
    (focus : Occurrence r) : ¬ GeneralNominalSupport.Discharged journal focus := by
  intro done
  induction done with
  | packet recorded member children ih =>
    have existsChild : ∃ child, child ∈ recorded.children := by
      cases shape : recorded.children with
      | nil => exact False.elim (nonterminal recorded member shape)
      | cons first rest => exact ⟨first,by simp⟩
    obtain ⟨child,included⟩ := existsChild
    exact ih child included
  | alias first last firstMember lastMember same done ih => exact ih

/-- The inductive settlement ledger is not semantic dictionary completion.
This fixture has one nonterminal packet but no leaf packet. -/
theorem no_discharged (focus : Occurrence roles) :
    ¬ GeneralNominalSupport.Discharged finish.current focus := by
  apply no_discharge_without_terminal_packet finish.current
  intro recorded member
  have same : recorded = packet := List.mem_singleton.mp member
  subst recorded
  rw [children_exact]
  simp

theorem packet_unsettled : GeneralNominalSettledSupport.Unsettled finish.current packet :=
  ⟨List.mem_singleton_self packet,displayChild,by rw [children_exact]; simp,no_discharged displayChild⟩

/-- Even this stable successful semantic dictionary does not authorize using
its un-settled packet outputs as trusted head explanations. -/
theorem output_not_trusted (facts : List (GeneralNominalSupport.Fact roles))
    (trusted : GeneralNominalSettledSupport.Trusted finish facts)
    (support : List (Occurrence roles)) :
    GeneralNominalSupport.Fact.outputs packet support ∉ facts :=
  GeneralNominalSettledSupport.no_unsettled_output trusted packet_unsettled

end Yulang.GeneralDictionarySettledRecursiveExample
