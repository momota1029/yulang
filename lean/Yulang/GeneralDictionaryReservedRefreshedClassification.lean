import Yulang.GeneralDictionaryReservedRefreshedEvidence

/-! Exact selected classification after the real carrier-changing nominal refresh.
Stability is established separately by exhaustive transition analysis. -/
namespace Yulang.GeneralDictionaryReservedRefreshedClassification
set_option backward.isDefEq.respectTransparency false
open GeneralDictionaryFiniteObservedExampleReserved
open GeneralDictionaryFiniteObservedExampleReservedPositive
open GeneralDictionaryFiniteObservedExample (registry declaration checked descriptor)
open GeneralDictionaryReservedRefreshedEvidence GeneralDictionaryReservedNominalRefresh
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralNominalSaturationState GeneralNominalSupport
open GeneralDeclarationExamples (roles)
open CommonNominalFullCarrier
noncomputable abbrev current := refreshed.current.context

private theorem int_not_nominal (name : Nat) (args : List Argument) :
    ¬ Subtype (.base .int) (nominal name args) := by
  intro below
  exact (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (below 0) 0
    ⟨fun _ => .bottom,fun _ => []⟩ (.nominalHead name args.length) ⟨rfl,by simp⟩
private theorem no_raw_recurs : ¬ GeneralNominalCycleK2.RecursAt current.state (1 : Fin 3) := by
  intro recurs
  obtain ⟨next,edge,_⟩ := GeneralNominalCycleK2.recurs_cycle current.state (1 : Fin 3) recurs
  rcases edge with ⟨kind,_,_,_⟩ | ⟨desc,recorded,_⟩
  · exact Fin.elim0 kind
  · cases recorded
private theorem no_feedback_cycle : ¬ GeneralNominalFeedbackK2.Cycle refreshed.current 1 := by
  rintro ⟨next,edge,_⟩
  rcases edge.2.2 with ⟨_,_,⟨kind,_,_,_⟩,_,_⟩ | ⟨name,index,observes⟩
  · exact Fin.elim0 kind
  · obtain ⟨actual,seen,_⟩ := observes positive refreshed_inhabited
    cases seen with
    | argument parent equal found =>
      cases parent
      exact int_not_nominal _ _ equal.1
private theorem no_root : ¬ GeneralNominalFeedbackK2.RootK2 refreshed.current root := by
  rintro (⟨_,_,_,slot,same,cycle⟩ | ⟨_,_,_,cycle,_⟩)
  · have one : slot = (1 : Fin 3) := Fin.ext same
    subst slot; exact no_raw_recurs cycle
  · exact no_feedback_cycle cycle
private theorem no_candidate : ¬ GeneralNominalFeedbackK2.CandidateK2 registry refreshed.current root := by
  rintro (⟨_,decl,visible,check,_,_,bounds,located,visited,member,cycle⟩ |
    ⟨_,decl,visible,check,_,_,bounds,located,visited,member,cycle,_⟩)
  all_goals
    have eq : decl = declaration := List.mem_singleton.mp visible
    subst decl
    have one : bounds = [((1 : Fin 3),(1 : Fin 3))] := Option.some.inj (located.symm.trans (by decide +kernel))
    subst bounds
    have v : visited = ((1 : Fin 3),(1 : Fin 3)) := by
      have inspected : (report current declaration [((1 : Fin 3),(1 : Fin 3))]).inspected = [((1 : Fin 3),(1 : Fin 3))] := by
        simp only [report, shape.query, inspectMany, inspect, shape.noNominal, shape.head,
          ↓reduceIte, Report.visit, Report.append, List.append_nil]
      rw [inspected] at member
      exact List.mem_singleton.mp member
    subst visited
  · exact no_raw_recurs cycle
  · exact no_feedback_cycle cycle
private theorem root_ready : ¬ GeneralNominalState.RootPending current.state root.demand := by
  rintro ⟨index,unknown⟩
  exact unknown ⟨(1 : Fin 3),rfl,Or.inl (by decide +kernel)⟩
private theorem prepared : Prepared registry current root declaration checked := by
  obtain ⟨decl,visible,check,key,role,bounds,located,finished,requested,emitted,catalogue,branch⟩ :=
    current_instance positive refreshed_inhabited
  have same : decl = declaration := List.mem_singleton.mp visible
  subst decl
  refine ⟨catalogue,?_,?_,bounds,located,finished,requested,positive,branch⟩
  · constructor
    · intro index; change (1 ∈ GeneralNominalState.sources current.state ∧ 1 ∈ GeneralNominalState.sources current.state); decide +kernel
    · intro output member
      have same := List.mem_singleton.mp member
      subst output
      decide +kernel
  · intro key member
    change key ∈ [] at member
    cases member
private theorem children_empty (check : GeneralDeclarations.DeclarationChecked registry.constructors roles declaration)
    (bounds : List (GeneralNominalInspection.Bounds current.state)) :
    GeneralNominalAllocation.children current.state registry root declaration check
      (bindings current.state (report current declaration bounds)) = [] :=
  GeneralDictionaryLinearLeaf.children_empty current registry root declaration check rfl _
private theorem survivor : Survivor registry current root declaration.id [] :=
  ⟨root_ready,declaration,by simp,checked,rfl,rfl,[((1 : Fin 3),(1 : Fin 3))],by decide +kernel,prepared,(children_empty checked _).symm⟩

theorem selected : GeneralNominalFeedbackK2.Local registry refreshed.current root (.selected declaration.id []) := by
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

theorem decisions : DecisionGuard refreshed registry root [] := by
  refine ⟨(by intro _ impossible; cases impossible),?_,?_⟩
  · intro index
    exact source_ready refreshed 1 (.scalar .int) _ _
      (Head.scalar (snapshot := state) 1 .int rfl)
      (Head.scalar (snapshot := current.state) (1 : Fin 3) .int rfl) []
  · intro decl visible role bounds located slot member
    have same : decl = declaration := List.mem_singleton.mp visible
    subst decl
    have pairs : bounds = [((1 : Fin 3),(1 : Fin 3))] :=
      Option.some.inj (located.symm.trans (by decide +kernel))
    subst bounds
    have seen : readsMany current.state
        (GeneralNominalInspection.queries current.state current.interpretation declaration)
        [((1 : Fin 3),(1 : Fin 3))] = [(1 : Fin 3)] := by simp only [shape.query, readsMany, reads, List.append_nil]
    rw [seen] at member
    have one := List.mem_singleton.mp member
    subst slot
    exact source_ready refreshed 1 (.scalar .int) _ _
      (Head.scalar (snapshot := state) 1 .int rfl)
      (Head.scalar (snapshot := current.state) (1 : Fin 3) .int rfl) []

theorem value_selected : GeneralNominalValueBoundary.Local registry refreshed root (.selected declaration.id []) :=
  GeneralNominalValueBoundary.selected_supported selected []
    (GeneralNominalValueSupport.source_decision registry refreshed root decisions)

theorem classified : B4TargetV3.Classify (GeneralNominalValueBoundary.boundary roles).toSourceBoundary
    registry refreshed root (.selected (.node declaration.id [])) := by
  have chosen := (GeneralNominalValueBoundary.local_correspondence registry refreshed root _).mpr value_selected
  cases chosen with
  | selected safe unique => exact .selected safe unique .nil


end Yulang.GeneralDictionaryReservedRefreshedClassification
