import Yulang.GeneralDictionaryFiniteObservedExampleReserved
import Yulang.GeneralNominalValueBoundary

namespace Yulang.GeneralDictionaryFiniteObservedExampleReservedPositive
open GeneralDictionaryFiniteObservedExampleReserved
open GeneralDictionaryFiniteObservedExample (model arguments interpretation declaration registry checked equation descriptor)
open GeneralNominalMaterialization GeneralNominalRecursiveInspection
open CommonNominalFullCarrier
abbrev positive : GeneralNominalCommonBridge.Assignment := fun source =>
  if source = 2 then (nominal 0 arguments,Common.rowEmpty) else model source

theorem positive_source : GeneralNominalState.Models state positive := by
  have low : ∀ slot : Fin 2, positive slot.val = model slot.val := by
    intro slot
    simp [positive,show slot.val ≠ 2 by omega]
  have assigned : GeneralNominalCommonBridge.assignment state.base positive =
      GeneralNominalCommonBridge.assignment state.base model := by
    funext slot; exact low slot
  refine ⟨⟨?_,?_,?_⟩,?_,PresenceNormalForm.all_nil _ _⟩
  · change PresenceNormalForm.All CommonNominalFullCarrier.model (GeneralNominalCommonBridge.assignment state.base positive) _
    rw [assigned]
    exact source_models.1.1
  · intro slot term recorded
    have original := source_models.1.2.1 slot term recorded
    change Equivalent (positive slot.val).1 (term.eval CommonNominalFullCarrier.model (GeneralNominalCommonBridge.assignment state.base positive))
    rw [low slot,assigned]
    exact original
  · intro pair member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> exact subtype_refl _
  · intro slot descriptor recorded
    obtain ⟨values,fits,equal⟩ := source_models.2.1 slot descriptor recorded
    refine ⟨values,?_,?_⟩
    · have transform : ∀ parameters values, GeneralNominalState.FitsAll state.base model parameters values → GeneralNominalState.FitsAll state.base positive parameters values := by
        intro parameters values fits
        induction fits with
        | nil => exact .nil
        | @cons parameter value parameters values head tail ih =>
          refine .cons ?_ ih
          cases parameter <;> cases value <;> first | exact head | simpa [GeneralNominalState.Fits,low] using head
      exact transform _ _ fits
    · simpa [low] using equal

theorem positive_request (capture : GeneralDeclarationDemands.Capture) (report : Report state) :
    Models state declaration capture report (generated state interpretation [request]) positive := by
  have empty : (generated state interpretation [request]).variables = [] := by
    simp [GeneralNominalMaterialization.generated,request,GeneralNominalInspection.translate,GeneralDeclarationPatterns.normalize,
      GeneralDeclarationPatterns.normalizeArgs,interpretation,
      GeneralDictionaryFiniteObservedExample.interpretation,GeneralNominalExamples.interpretation,
      GeneralDictionaryFiniteObservedExample.constructors,schema,schemas,Schema.append]
  refine ⟨?_,?_,?_,?_⟩
  · intro test member
    rw [tests_exact] at member
    have child : ∀ index, index < 3 →
        (∃ actual, Observes positive (.nominal (.source 2) 0 index) actual) ∧
        ∀ actual, Observes positive (.nominal (.source 2) 0 index) actual → Equivalent actual (.base .int) := by
      intro index bound
      have nth : arguments[index]? = some (.inl (.base .int)) := by
        have cases : index = 0 ∨ index = 1 ∨ index = 2 := by omega
        rcases cases with rfl | rfl | rfl <;> rfl
      refine ⟨⟨.base .int,.nominal (.source 2) ⟨subtype_refl _,subtype_refl _⟩ nth⟩,?_⟩
      intro actual seen
      cases seen with
      | nominal parent equal found =>
        cases parent
        have invariant := (nominal_regular_invariant_exact _ _ _ _).mp equal.1
        exact ⟨(invariant.2.2 index _ _ nth found).2,(invariant.2.2 index _ _ nth found).1⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · refine ⟨⟨_,.source 2⟩,?_⟩
      intro actual seen; cases seen
      exact ⟨arguments,rfl,⟨subtype_refl _,subtype_refl _⟩⟩
    · exact child 0 (by decide)
    · exact child 1 (by decide)
    · exact child 2 (by decide)
  · intro entry member; rw [empty] at member; cases member
  · intro entry member; rw [empty] at member; cases member
  · intro entry member; rw [empty] at member; cases member

open GeneralNominalRecursiveCandidates GeneralDictionaryRecursiveEvidence
open GeneralDeclarationPatterns GeneralDeclarations
open GeneralDeclarationExamples (roles)
open GeneralNominalSupport GeneralNominalSaturationState
abbrev metadata := initial_source.metadata
theorem report_exact : report context declaration [(1,1)] =
    { inspected := [(1,1)], checked := [(1,1),(1,1)] } := by
  simp [report,GeneralNominalInspection.queries,Declaration.normalHead,
    normalizeArgs,normalize,GeneralNominalInspection.translate,interpretation,
    GeneralNominalExamples.interpretation,inspectMany,inspect,
    Report.visit,Report.append]

theorem branch_models :
    BranchModels registry context root declaration checked [(1,1)] positive := by
  refine ⟨?_,?_,?_⟩
  · unfold privateState
    rw [report_exact]
    apply (GeneralNominalState.extend_models ..).mpr
    refine ⟨(GeneralNominalAllocation.propagate_models ..).mpr ⟨positive_source,?_,?_⟩,?_⟩
    · simp [bindings,GeneralNominalAllocation.Compatible]
    · simp [bindings,GeneralNominalAllocation.merges,Declaration.inputNames,normalizeArgs,normalize,variablesArgs,Pattern.variables]
    · simp [selfChecks,PresenceNormalForm.All]
      exact CommonNominalFullCarrier.subtype_refl _
  · rw [report_exact]
    simp [ProjectionModels]
  · unfold GeneralNominalRecursiveCandidates.generated; rw [actual_requests_exact]; exact positive_request _ _

theorem ready : RequestReady registry context root declaration checked [(1,1)] := by
  constructor
  · intro output member
    have same := List.mem_singleton.mp member
    subst output
    exact ⟨equation,List.mem_singleton_self _,rfl⟩
  · unfold GeneralNominalRecursiveCandidates.generated
    rw [actual_requests_exact]
    simp [GeneralNominalMaterialization.generated,request,GeneralNominalInspection.translate,GeneralDeclarationPatterns.normalize,
      GeneralDeclarationPatterns.normalizeArgs,interpretation,
      GeneralDictionaryFiniteObservedExample.interpretation,GeneralNominalExamples.interpretation,
      GeneralDictionaryFiniteObservedExample.constructors,schema,schemas,Schema.append]
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
  · obtain ⟨actual,seen,_⟩ := observes model ((GeneralNominalSaturationState.initial_models context root model).mpr source_models)
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
    [(1,1)],by decide +kernel,?_,ready,positive,branch_models⟩
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


abbrev packet : Packet roles :=
  ⟨registry,context,GeneralNominalDemandMerging.pointSite root,declaration,checked,[(1,1)]⟩
theorem joint : GeneralNominalJointCandidates.Joint registry start.current root declaration.id :=
  GeneralNominalJointCandidates.initial_joint registry context root declaration (by simp) checked rfl
    [(1,1)] (by decide +kernel) prepared positive branch_models

theorem packet_children : packet.children = [] := children_empty

theorem enabled : GeneralNominalFeedbackSteps.Installable registry start.current packet := by
  refine ⟨?_,?_,?_⟩
  · refine ⟨rfl,rfl,by simp [start,GeneralNominalSupport.initial,GeneralNominalSaturationState.initial],by simp,rfl,rfl,prepared,?_,?_,?_,?_,?_⟩
    · rw [packet_children]
      exact GeneralNominalFeedbackK2.selected_legacy selected
    · intro prior member; cases member
    · intro other member _
      have same := List.mem_singleton.mp member
      subst other
      exact .refl _
    · exact ⟨positive,(GeneralNominalSaturationState.initial_models context root positive).mpr positive_source,branch_models⟩
    · exact joint
  · rw [packet_children]; exact selected
  · intro other member _
    have same := List.mem_singleton.mp member
    subst other
    exact .refl _

theorem novel : ¬ GeneralNominalFeedbackSteps.Committed start.current packet := by
  intro committed
  have valid := committed.1 model ((GeneralNominalSaturationState.initial_models context root model).mpr source_models)
  have branch := (GeneralNominalPacketSupport.packet_exact packet model).mp valid
  have bad := branch.2.2
  change GeneralNominalMaterialization.Models state declaration _ _
    (GeneralNominalMaterialization.generated state interpretation (requests state registry root declaration checked _)) model at bad
  rw [actual_requests_exact] at bad
  exact (initial_countermodel _ _).2 bad

theorem guard : GeneralNominalSupportSteps.PacketGuard start packet [] :=
  ⟨⟨decisions.1,decisions.2.1,decisions.2.2 declaration (by simp) rfl _ (by decide +kernel)⟩,decisions⟩
noncomputable abbrev installed := GeneralNominalSupportSteps.install start packet []
theorem value_install_step : GeneralNominalValueSteps.Step registry root start installed :=
  GeneralNominalValueSteps.source_install start packet .root enabled novel guard

theorem installed_models : GeneralNominalSaturationState.Models installed.current positive := by
  apply (GeneralNominalFeedbackSites.install_models start.current packet _ rfl positive).mpr
  exact ⟨(GeneralNominalSaturationState.initial_models context root positive).mpr positive_source,branch_models⟩

theorem value_reachable :
    B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root installed :=
  ⟨start,⟨context,initial_source,rfl⟩,.tail .refl value_install_step⟩

theorem packet_recorded : packet ∈ installed.current.packets := by
  exact List.mem_cons_self

theorem journal_nonempty : installed.current.packets ≠ [] := by
  intro impossible
  have member := packet_recorded
  rw [impossible] at member
  cases member
end Yulang.GeneralDictionaryFiniteObservedExampleReservedPositive
