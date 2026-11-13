import Yulang.GeneralDictionaryReservedEqualityStep

/-! Exact selected classification coexists with a still-enabled saturation step.
This is not a stable final-state classification claim. -/
namespace Yulang.GeneralDictionaryReservedInstalledClassification
set_option backward.isDefEq.respectTransparency false
open GeneralDictionaryFiniteObservedExampleReserved
open GeneralDictionaryFiniteObservedExampleReservedPositive
open GeneralDictionaryFiniteObservedExample (registry declaration checked descriptor)
open GeneralDictionaryReservedInstalledEvidence GeneralDictionaryReservedEqualityStep
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralNominalSaturationState GeneralNominalSupport
open GeneralDeclarationExamples (roles)
open CommonNominalFullCarrier
noncomputable abbrev current := installed.current.context

private theorem int_not_nominal (name : Nat) (args : List Argument) :
    ¬ Subtype (.base .int) (nominal name args) := by
  intro below
  exact (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (below 0) 0
    ⟨fun _ => .bottom,fun _ => []⟩ (.nominalHead name args.length) ⟨rfl,by simp⟩
private theorem no_raw_recurs : ¬ GeneralNominalCycleK2.RecursAt current.state (1 : Fin 2) := by
  intro recurs
  obtain ⟨next,edge,_⟩ := GeneralNominalCycleK2.recurs_cycle current.state (1 : Fin 2) recurs
  rcases edge with ⟨kind,_,_,_⟩ | ⟨desc,recorded,_⟩
  · exact Fin.elim0 kind
  · cases recorded
private theorem no_feedback_cycle : ¬ GeneralNominalFeedbackK2.Cycle installed.current 1 := by
  rintro ⟨next,edge,_⟩
  rcases edge.2.2 with ⟨_,_,⟨kind,_,_,_⟩,_,_⟩ | ⟨name,index,observes⟩
  · exact Fin.elim0 kind
  · obtain ⟨actual,seen,_⟩ := observes positive installed_models
    cases seen with
    | argument parent equal found =>
      cases parent
      exact int_not_nominal _ _ equal.1
private theorem no_root : ¬ GeneralNominalFeedbackK2.RootK2 installed.current root := by
  rintro (⟨_,_,_,slot,same,cycle⟩ | ⟨_,_,_,cycle,_⟩)
  · have one : slot = (1 : Fin 2) := Fin.ext same
    subst slot; exact no_raw_recurs cycle
  · exact no_feedback_cycle cycle
private theorem no_candidate : ¬ GeneralNominalFeedbackK2.CandidateK2 registry installed.current root := by
  rintro (⟨_,decl,visible,check,_,_,bounds,located,visited,member,cycle⟩ |
    ⟨_,decl,visible,check,_,_,bounds,located,visited,member,cycle,_⟩)
  all_goals
    have eq : decl = declaration := List.mem_singleton.mp visible
    subst decl
    have one : bounds = [((1 : Fin 2),(1 : Fin 2))] := Option.some.inj (located.symm.trans (by decide +kernel))
    subst bounds
    have v : visited = ((1 : Fin 2),(1 : Fin 2)) := by
      have inspected : (report current declaration [((1 : Fin 2),(1 : Fin 2))]).inspected = [((1 : Fin 2),(1 : Fin 2))] := by
        simp [report,GeneralNominalInspection.queries,GeneralDeclarations.Declaration.normalHead,
          GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
          GeneralNominalInspection.translate,GeneralDictionaryFiniteObservedExample.interpretation,
          GeneralNominalExamples.interpretation,inspectMany,inspect,Report.visit,Report.append,
          current,installed,GeneralNominalSupportSteps.install,GeneralNominalFeedbackSites.install,
          Packet.privateContext,privateState,GeneralNominalState.extend,GeneralNominalAllocation.propagate]
      rw [inspected] at member
      exact List.mem_singleton.mp member
    subst visited
  · exact no_raw_recurs cycle
  · exact no_feedback_cycle cycle
private theorem root_ready : ¬ GeneralNominalState.RootPending current.state root.demand := by
  rintro ⟨index,unknown⟩
  exact unknown ⟨(1 : Fin 2),rfl,Or.inl (by decide +kernel)⟩
private theorem prepared : Prepared registry current root declaration checked := by
  obtain ⟨decl,visible,check,key,role,bounds,located,finished,requested,emitted,catalogue,branch⟩ :=
    current_instance positive installed_models
  have same : decl = declaration := List.mem_singleton.mp visible
  subst decl
  refine ⟨catalogue,?_,?_,bounds,located,finished,requested,positive,branch⟩
  · exact GeneralNominalRefinements.linked
      (GeneralNominalRefinements.installed registry context root declaration [(1,1)]) root.demand initial_source.linked
  · intro key member
    change key ∈ [] at member
    cases member
private theorem children_empty (check : GeneralDeclarations.DeclarationChecked registry.constructors roles declaration)
    (bounds : List (GeneralNominalInspection.Bounds current.state)) :
    GeneralNominalAllocation.children current.state registry root declaration check
      (bindings current.state (report current declaration bounds)) = [] :=
  GeneralDictionaryLinearLeaf.children_empty current registry root declaration check rfl _
private theorem survivor : Survivor registry current root declaration.id [] :=
  ⟨root_ready,declaration,by simp,checked,rfl,rfl,[((1 : Fin 2),(1 : Fin 2))],by decide +kernel,prepared,(children_empty checked _).symm⟩

theorem selected : GeneralNominalFeedbackK2.Local registry installed.current root (.selected declaration.id []) := by
  refine .selected ⟨root_ready,no_root,no_candidate,?_⟩ ⟨survivor,?_⟩
  · rintro (old | ⟨_,legacy⟩)
    · obtain ⟨_,decl,visible,check,_,_,absent⟩ := old
      have eq : decl = declaration := List.mem_singleton.mp visible
      subst decl
      exact absent prepared
    · rcases legacy with ⟨⟨_,_,_,_,_,⟨⟨kind,_,_⟩,_⟩⟩,_⟩ |
        ⟨⟨_,_,_,_,_,_,_,_,_,_,⟨⟨kind,_,_⟩,_⟩⟩,_⟩ <;> exact Fin.elim0 kind
  · rintro key kids ⟨_,decl,visible,check,identity,role,bounds,located,ready,emitted⟩
    have eq : decl = declaration := List.mem_singleton.mp visible
    subst decl
    exact ⟨identity.symm,emitted.trans (children_empty check bounds)⟩

theorem decisions : DecisionGuard installed registry root [] := by
  refine ⟨(by intro _ impossible; cases impossible),?_,?_⟩
  · intro index
    exact source_ready installed 1 (.scalar .int) _ _
      (Head.scalar (snapshot := state) 1 .int rfl)
      (Head.scalar (snapshot := current.state) (1 : Fin 2) .int rfl) []
  · intro decl visible role bounds located slot member
    have bounded := slot.isLt
    change slot.val < 2 at bounded
    by_cases zero : slot.val = 0
    · have same : slot = (0 : Fin 2) := Fin.ext zero
      subst slot
      exact source_ready installed 0 (.nominal 0 3) _ _
        (Head.nominal (snapshot := state) 0 descriptor rfl)
        (Head.nominal (snapshot := current.state) (0 : Fin 2) descriptor rfl) []
    · have same : slot = (1 : Fin 2) := by apply Fin.ext; change slot.val = 1; omega
      subst slot
      exact source_ready installed 1 (.scalar .int) _ _
        (Head.scalar (snapshot := state) 1 .int rfl)
        (Head.scalar (snapshot := current.state) (1 : Fin 2) .int rfl) []

theorem value_selected : GeneralNominalValueBoundary.Local registry installed root (.selected declaration.id []) :=
  GeneralNominalValueBoundary.selected_supported selected []
    (GeneralNominalValueSupport.source_decision registry installed root decisions)

theorem classified : B4TargetV3.Classify (GeneralNominalValueBoundary.boundary roles).toSourceBoundary
    registry installed root (.selected (.node declaration.id [])) := by
  have chosen := (GeneralNominalValueBoundary.local_correspondence registry installed root _).mpr value_selected
  cases chosen with
  | selected safe unique => exact .selected safe unique .nil

theorem selected_not_yet_stable :
    B4TargetV3.Classify (GeneralNominalValueBoundary.boundary roles).toSourceBoundary registry installed root
      (.selected (.node declaration.id [])) ∧
    (¬ GeneralNominalValueSteps.Stable registry installed root) ∧
    ∀ assignment, Models installed.current assignment →
      GeneralDictionaryRecursiveEvidence.Evidence registry current assignment root (.node declaration.id []) :=
  ⟨classified,installed_not_stable,current_evidence⟩
end Yulang.GeneralDictionaryReservedInstalledClassification
