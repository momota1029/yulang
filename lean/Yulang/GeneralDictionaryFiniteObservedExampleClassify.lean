import Yulang.GeneralDictionaryFiniteObservedExampleStable
import Yulang.GeneralNominalValueBoundary

/-! Exact classification of the stable zero-step ternary named-output fixture.
The semantic output model and every cycle exclusion are concrete. -/
namespace Yulang.GeneralDictionaryFiniteObservedExampleClassify
open GeneralDictionaryFiniteObservedExample GeneralDictionaryFiniteObservedExampleStable
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralNominalSupport GeneralNominalSaturationState
open GeneralDeclarationExamples (roles)
open CommonNominalFullCarrier

private theorem int_not_nominal (name : Nat) (args : List Argument) :
    ¬ Subtype (.base .int) (nominal name args) := by
  intro below
  exact (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (below 0) 0
    ⟨fun _ => .bottom,fun _ => []⟩ (.nominalHead name args.length) ⟨rfl,by simp⟩

private theorem no_raw_recurs : ¬ GeneralNominalCycleK2.RecursAt state (1 : Fin 2) := by
  intro recurs
  obtain ⟨next,edge,_⟩ := GeneralNominalCycleK2.recurs_cycle state 1 recurs
  rcases edge with ⟨kind,_,_,_⟩ | ⟨desc,recorded,_⟩
  · exact Fin.elim0 kind
  · cases recorded

private theorem no_feedback_cycle : ¬ GeneralNominalFeedbackK2.Cycle start.current 1 := by
  rintro ⟨next,edge,_⟩
  rcases edge.2.2 with ⟨_,_,⟨kind,_,_,_⟩,_,_⟩ | ⟨name,index,observes⟩
  · exact Fin.elim0 kind
  · obtain ⟨actual,seen,_⟩ := observes model (initial_models model state_models)
    cases seen with
    | argument parent compared _ =>
      cases parent
      exact int_not_nominal _ _ compared.1

theorem no_root : ¬ GeneralNominalFeedbackK2.RootK2 start.current root := by
  rintro (⟨_,_,_,slot,same,cycle⟩ | ⟨_,_,_,cycle,_⟩)
  · have one : slot = (1 : Fin 2) := Fin.ext same
    subst slot; exact no_raw_recurs cycle
  · exact no_feedback_cycle cycle

theorem no_candidate : ¬ GeneralNominalFeedbackK2.CandidateK2 registry start.current root := by
  rintro (⟨_,decl,visible,check,_,_,bounds,located,visited,member,cycle⟩ |
    ⟨_,decl,visible,check,_,_,bounds,located,visited,member,cycle,_⟩)
  all_goals
    have eq : decl = declaration := List.mem_singleton.mp visible
    subst decl
    have one : bounds = [((1 : Fin 2),(1 : Fin 2))] := Option.some.inj (located.symm.trans (by decide +kernel))
    subst bounds
    change visited ∈ (report context declaration [(1,1)]).inspected at member
    rw [report_exact] at member
    have v : visited = ((1 : Fin 2),(1 : Fin 2)) := List.mem_singleton.mp member
    subst visited
  · exact no_raw_recurs cycle
  · exact no_feedback_cycle cycle

theorem root_ready : ¬ GeneralNominalState.RootPending state root.demand := by
  rintro ⟨index,unknown⟩
  exact unknown ⟨(1 : Fin 2),rfl,Or.inl (by decide +kernel)⟩

theorem prepared : Prepared registry context root declaration checked := by
  refine ⟨metadata,initial_source.linked,
    GeneralNominalSourceFormation.initial_fresh context initial_source root.identity,
    [(1,1)],by decide +kernel,?_,ready,model,branch_models model state_models⟩
  rw [report_exact]
  exact ⟨rfl,rfl,rfl⟩

theorem children_empty : GeneralNominalAllocation.children state registry root declaration checked
    (bindings state (report context declaration [(1,1)])) = [] :=
  GeneralDictionaryLinearLeaf.children_empty context registry root declaration checked rfl _

theorem survivor : Survivor registry context root declaration.id [] :=
  ⟨root_ready,declaration,by simp,checked,rfl,rfl,[(1,1)],by decide +kernel,prepared,children_empty.symm⟩

theorem unique : GeneralNominalLocalBoundary.Unique (GeneralNominalFeedbackK2.fields roles)
    registry start.current root declaration.id [] := by
  refine ⟨survivor,?_⟩
  rintro key kids ⟨_,decl,visible,check,identity,role,bounds,located,ready,emitted⟩
  have eq : decl = declaration := List.mem_singleton.mp visible
  subst decl
  have eq : bounds = [((1 : Fin 2),(1 : Fin 2))] := Option.some.inj (located.symm.trans (by decide +kernel))
  subst bounds
  refine ⟨identity.symm,?_⟩
  exact emitted.trans children_empty

theorem selected : GeneralNominalFeedbackK2.Local registry start.current root
    (.selected declaration.id []) := by
  refine .selected ⟨root_ready,no_root,no_candidate,?_⟩ unique
  rintro (old | ⟨_,legacy⟩)
  · obtain ⟨_,decl,visible,check,_,_,absent⟩ := old
    have eq : decl = declaration := List.mem_singleton.mp visible
    subst decl
    exact absent prepared
  · rcases legacy with ⟨⟨_,_,_,_,_,⟨⟨kind,_,_⟩,_⟩⟩,_⟩ |
        ⟨⟨_,_,_,_,_,_,_,_,_,_,⟨⟨kind,_,_⟩,_⟩⟩,_⟩ <;> exact Fin.elim0 kind

theorem decisions : DecisionGuard start registry root [] := by
  refine ⟨(by intro _ impossible; cases impossible),?_,?_⟩
  · intro index
    exact source_ready start 1 (.scalar .int) _ _
      (Head.scalar (snapshot := state) 1 .int rfl)
      (Head.scalar (snapshot := state) 1 .int rfl) []
  · intro decl visible role bounds located slot member
    have bounded := slot.isLt
    change slot.val < 2 at bounded
    by_cases zero : slot.val = 0
    · have same : slot = (0 : Fin 2) := Fin.ext zero
      subst slot
      exact source_ready start 0 (.nominal 0 3) _ _
        (Head.nominal (snapshot := state) 0 descriptor rfl)
        (Head.nominal (snapshot := state) 0 descriptor rfl) []
    · have same : slot = (1 : Fin 2) := by apply Fin.ext; change slot.val = 1; omega
      subst slot
      exact source_ready start 1 (.scalar .int) _ _
        (Head.scalar (snapshot := state) 1 .int rfl)
        (Head.scalar (snapshot := state) 1 .int rfl) []

theorem support_selected : GeneralNominalSupportBoundary.Local registry start root
    (.selected declaration.id []) :=
  GeneralNominalSupportBoundary.selected_supported selected [] decisions

theorem classified : B4TargetV3.Classify (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary
    registry start root (.selected (.node declaration.id [])) := by
  have selected := (GeneralNominalSupportBoundary.local_correspondence registry start root _).mpr support_selected
  cases selected with
  | selected safe unique => exact .selected safe unique .nil

theorem stable_classified_named_dictionary :
    B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry root start ∧
    Models start.current model ∧ GeneralNominalSupportSteps.Stable registry start root ∧
    B4TargetV3.Classify (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary
      registry start root (.selected (.node declaration.id [])) ∧
    root.demand.outputs ≠ [] ∧
    ∀ assignment, Models start.current assignment →
      GeneralDictionaryRecursiveEvidence.Evidence registry context assignment root (.node declaration.id []) :=
  ⟨actual_reachable,initial_models model state_models,stable,classified,named_request_present,fun m valid => full_evidence m valid.1⟩
/-- The stronger captured-value boundary uses source-supported decisions here. -/
theorem value_selected : GeneralNominalValueBoundary.Local registry start root
    (.selected declaration.id []) :=
  GeneralNominalValueBoundary.selected_supported selected []
    (GeneralNominalValueSupport.source_decision registry start root decisions)

theorem value_stable : GeneralNominalValueSteps.Stable registry start root := by
  intro focus reached next update
  exact stable focus reached next
    (GeneralNominalDownstreamSteps.at_old (GeneralNominalValueSteps.at_old update))

theorem value_reachable :
    B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root start :=
  ⟨start,⟨context,initial_source,rfl⟩,.refl⟩

theorem value_classified : B4TargetV3.Classify (GeneralNominalValueBoundary.boundary roles).toSourceBoundary
    registry start root (.selected (.node declaration.id [])) := by
  have chosen := (GeneralNominalValueBoundary.local_correspondence registry start root _).mpr value_selected
  cases chosen with
  | selected safe unique => exact .selected safe unique .nil

/-- Actual initial-source zero-step execution, stable classification and full
ternary-output evidence under the newest additive value-provenance boundary. -/
theorem value_stable_classified_named_dictionary :
    B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root start ∧
    Models start.current model ∧ GeneralNominalValueSteps.Stable registry start root ∧
    B4TargetV3.Classify (GeneralNominalValueBoundary.boundary roles).toSourceBoundary
      registry start root (.selected (.node declaration.id [])) ∧
    root.demand.outputs ≠ [] ∧
    ∀ assignment, Models start.current assignment →
      GeneralDictionaryRecursiveEvidence.Evidence registry context assignment root (.node declaration.id []) :=
  ⟨value_reachable,initial_models model state_models,value_stable,value_classified,named_request_present,
    fun m valid => full_evidence m valid.1⟩
end Yulang.GeneralDictionaryFiniteObservedExampleClassify
