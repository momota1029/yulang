import Yulang.GeneralNominalFeedbackRefresh
import Yulang.GeneralNominalCanonicalSiteObstruction

/-! End-to-end finite regression for journal recursion, and repairs of the
nonpoint-origin and equal-endpoint merging obstructions on the general carrier. -/
namespace Yulang.GeneralNominalFeedbackRegressions

open GeneralNominalFeedbackObstruction
open GeneralNominalSaturationState GeneralNominalFeedbackSites GeneralSourceDictionaries
open GeneralNominalRecursiveInspection CommonNominalFullCarrier
open GeneralDeclarationExamples (roles)

private theorem int_not_nominal (name : Nat) (arguments : List Argument) : ¬ Subtype (.base .int) (nominal name arguments) := by
  intro below
  exact (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (below 0) 0
    ⟨fun _ => .bottom,fun _ => []⟩ (.nominalHead name arguments.length) ⟨rfl,by simp⟩

private theorem edge_bounds (first last : Nat) (edge : GeneralNominalFeedbackK2.Edge initialState first last) :
    first < 2 ∧ ¬ last < 2 := by
  rcases edge.2.2 with ⟨parent,child,⟨kind,_,_,_,_⟩,_,_⟩ | ⟨name,index,observed⟩
  · exact Fin.elim0 kind
  · obtain ⟨actual,seen,equal⟩ := observed finiteModel ((initial_models context root finiteModel).mpr finite_source_models)
    cases seen with
    | argument parent compared found =>
      cases parent
      have small : first < 2 := by
        by_cases small : first < 2
        · exact small
        · have impossible := compared.1
          simp only [small] at impossible
          exact False.elim (int_not_nominal _ _ impossible)
      refine ⟨small,?_⟩
      intro lastSmall
      simp only [small] at compared
      have invariant := (nominal_regular_invariant_exact _ _ _ _).mp compared.1
      have size := invariant.2.1
      have zero : index = 0 := by
        obtain ⟨bound,_⟩ := List.getElem?_eq_some_iff.mp found
        simp only [List.length_cons,List.length_nil] at size
        omega
      subst index
      have arg := invariant.2.2 0 (.inl (.base .int)) (.inl actual) rfl found
      simp only [lastSmall] at equal
      exact int_not_nominal _ _ (subtype_trans arg.1 equal.1)

theorem initial_acyclic (source : Nat) : ¬ GeneralNominalFeedbackK2.Cycle initialState source := by
  rintro ⟨next,edge,path⟩
  have bounded := edge_bounds source next edge
  cases path with
  | nil => exact bounded.2 bounded.1
  | cons edge _ => exact bounded.2 (edge_bounds _ _ edge).1

theorem selected : GeneralNominalFeedbackK2.Local registry initialState root (.selected 2 [child]) := by
  cases old_selected with
  | selected safe unique =>
    refine .selected ⟨safe.1,?_,?_,safe.2.2.2⟩ unique
    · rintro (old | ⟨_,_,index,cycle,_⟩)
      · exact safe.2.1 old
      · exact initial_acyclic _ cycle
    · rintro (old | ⟨_,_,_,_,_,_,_,_,visited,_,cycle,_⟩)
      · exact safe.2.2.1 old
      · exact initial_acyclic _ cycle

theorem enabled : GeneralNominalFeedbackSteps.Installable registry initialState packet := by
  refine ⟨old_enabled,?_,?_⟩
  · change GeneralNominalFeedbackK2.Local registry initialState root (.selected 2 packet.children)
    rw [children_exact]; exact selected
  · intro other member _
    have same := List.mem_singleton.mp member; subst other
    exact .refl _

theorem install_step : GeneralNominalFeedbackSteps.Step registry root initialState installed := by
  refine ⟨root,.root,.install packet enabled ?_⟩
  intro committed
  have absent := committed.2 child (by rw [children_exact]; simp)
  cases absent

theorem formed : GeneralNominalFeedbackSteps.SourceFormed registry root installed :=
  .update (.initial context initial_source) install_step

theorem two_steps_reject_child :
    GeneralDeclarations.Checked registry ∧
    GeneralNominalFeedbackSteps.SourceFormed registry root GeneralNominalFeedbackRefresh.refreshed ∧
    B4Target.Steps (GeneralNominalFeedbackSteps.Step registry root) initialState GeneralNominalFeedbackRefresh.refreshed ∧
    Models GeneralNominalFeedbackRefresh.refreshed model ∧
    GeneralNominalFeedbackK2.Local registry GeneralNominalFeedbackRefresh.refreshed child .rejected :=
  ⟨checked,.update formed GeneralNominalFeedbackRefresh.refresh_step,
    .tail (.tail .refl install_step) GeneralNominalFeedbackRefresh.refresh_step,
    (GeneralNominalFeedbackRefresh.refresh_models model).mpr installed_models,GeneralNominalFeedbackRefresh.child_rejected⟩

theorem child_origin : OriginAt packet child 0 (.nominal (.source 0) 0 0) := by
  refine ⟨clause,by simp,declaration_checked.signature.2.2.2 clause (by simp),⟨0,by decide +kernel⟩,?_,rfl,
    ⟨0,(2,3),some (.nominal (.source 0) 0 0)⟩,?_,by decide +kernel,rfl,rfl⟩
  · have calculated : packet.bindings = [(0,(2,3))] := by unfold Packet.bindings; rw [report_exact]; rfl
    unfold clauseChild
    simp [GeneralDeclarationDemands.emit,GeneralDictionaryEmissionPlans.occurrence,
      GeneralDeclarationDemands.childDemand,GeneralDeclarationDemands.inputInterval,GeneralDeclarationDemands.outputTarget,
      frame,GeneralNominalAllocation.frame,GeneralNominalAllocation.capture,GeneralNominalAllocation.occurrences,
      GeneralDeclarationPatterns.normalize,GeneralDeclarations.Declaration.outputNames,
      GeneralNominalAllocation.allocation,child,output,calculated]
    exact ⟨rfl,rfl⟩
  · rw [report_exact]
    exact List.mem_singleton_self _

theorem nonpoint_origin_retained :
    (child.demand.arguments ⟨0,by decide +kernel⟩).1 ≠ (child.demand.arguments ⟨0,by decide +kernel⟩).2 ∧
    ∃ origin, (childSite packet child).inputs[0]? = some (some origin) ∧ OriginAt packet child 0 origin :=
  ⟨by decide +kernel,child_retains_origin packet child ⟨0,by decide +kernel⟩ ⟨_,child_origin⟩⟩

private theorem all₂_ofFn (first last : Fin n → α) (relation : α → α → Prop)
    (pointwise : ∀ index, relation (first index) (last index)) :
    GeneralNominalDemandMerging.All₂ relation (List.ofFn first) (List.ofFn last) := by
  induction n with
  | zero => simp only [List.ofFn_zero]; exact .nil
  | succ n ih =>
    rw [List.ofFn_succ,List.ofFn_succ]
    exact .cons (pointwise 0) (ih (fun i => first i.succ) (fun i => last i.succ) (fun i => pointwise i.succ))

theorem recovered_point_inputs (state : State roles') (root : Occurrence roles')
    (equal : ∀ index, EndpointEqual state (root.demand.arguments index)) :
    (recover state (GeneralNominalDemandMerging.pointSite root)).inputs =
      List.ofFn (fun index => some (Origin.source (root.demand.arguments index).1)) := by
  classical
  apply congrArg List.ofFn
  funext index
  change recoverOrigin state (GeneralNominalDemandMerging.pointSite root) index = _
  unfold recoverOrigin
  have entry : (GeneralNominalDemandMerging.pointSite root).inputs[index.val]'(by rw [(GeneralNominalDemandMerging.pointSite root).arity]; exact index.isLt) =
      (if (root.demand.arguments index).1 = (root.demand.arguments index).2 then
        some (.source (root.demand.arguments index).1) else none) := by
    simp only [GeneralNominalDemandMerging.pointSite,List.getElem_ofFn]
    rfl
  rw [entry]
  by_cases point : (root.demand.arguments index).1 = (root.demand.arguments index).2
  · rw [ite_eq_left point]
  · rw [ite_eq_right point]
    exact ite_eq_left (equal index)

theorem recovered_point_self (state : State roles') (root : Occurrence roles')
    (equal : ∀ index, EndpointEqual state (root.demand.arguments index)) :
    SameInputs state (GeneralNominalDemandMerging.pointSite root) (GeneralNominalDemandMerging.pointSite root) := by
  refine ⟨rfl,?_⟩
  rw [recovered_point_inputs state root equal]
  exact all₂_ofFn _ _ _ (fun i => ⟨_,_,rfl,rfl,GeneralNominalDemandMerging.source_same _ _⟩)

theorem equal_nonpoint_now_recognized :
    SameInputs (initial GeneralNominalCanonicalSiteObstruction.context GeneralNominalCanonicalSiteObstruction.root)
      (GeneralNominalDemandMerging.pointSite GeneralNominalCanonicalSiteObstruction.root)
      (GeneralNominalDemandMerging.pointSite GeneralNominalCanonicalSiteObstruction.root) := by
  apply recovered_point_self
  intro index m valid
  exact GeneralNominalCanonicalSiteObstruction.equivalent_endpoints m valid.1

abbrev mergeFirst : Occurrence roles := ⟨100,⟨1,fun _ => (0,1),[⟨0,2⟩],by
  intro o member; have same := List.mem_singleton.mp member; subst o; exact ⟨none,rfl⟩⟩⟩
abbrev mergeLast : Occurrence roles := ⟨101,⟨1,fun _ => (0,1),[⟨0,3⟩],by
  intro o member; have same := List.mem_singleton.mp member; subst o; exact ⟨none,rfl⟩⟩⟩
abbrev mergeState : State roles :=
  { context := GeneralNominalCanonicalSiteObstruction.context
    sites := [GeneralNominalDemandMerging.pointSite mergeFirst,GeneralNominalDemandMerging.pointSite mergeLast] }

theorem distinct_nonpoint_inputs_same : SameInputs mergeState
    (GeneralNominalDemandMerging.pointSite mergeFirst) (GeneralNominalDemandMerging.pointSite mergeLast) := by
  refine ⟨rfl,?_⟩
  rw [recovered_point_inputs mergeState mergeFirst (fun _ m valid =>
      GeneralNominalCanonicalSiteObstruction.equivalent_endpoints m valid.1),
    recovered_point_inputs mergeState mergeLast (fun _ m valid =>
      GeneralNominalCanonicalSiteObstruction.equivalent_endpoints m valid.1)]
  change GeneralNominalDemandMerging.All₂ _ [some (Origin.source 0)] [some (Origin.source 0)]
  exact .cons ⟨_,_,rfl,rfl,GeneralNominalDemandMerging.source_same _ _⟩ .nil

theorem distinct_nonpoint_merge_step : GeneralNominalFeedbackSteps.Step registry mergeFirst mergeState
    (merge mergeState (GeneralNominalDemandMerging.pointSite mergeFirst) (GeneralNominalDemandMerging.pointSite mergeLast)) := by
  refine ⟨mergeFirst,.root,.merge _ _ (by simp) (by simp) distinct_nonpoint_inputs_same ?_⟩
  intro alias
  have identity : ∀ first last, Alias mergeState first last → first = last := by
    intro first last equal
    induction equal with
    | refl => rfl
    | edge member => cases member
    | symm _ ih => exact ih.symm
    | trans _ _ one two => exact one.trans two
  have impossible : (100 : Nat) = 101 := identity _ _ alias
  contradiction

theorem distinct_nonpoint_output_equation (m : GeneralNominalCommonBridge.Assignment)
    (valid : Models (merge mergeState (GeneralNominalDemandMerging.pointSite mergeFirst)
      (GeneralNominalDemandMerging.pointSite mergeLast)) m) : Equivalent (m 2).1 (m 3).1 :=
  ((GeneralNominalDemandMerging.output_atoms_exact _ _ m).mp ((GeneralNominalSaturationState.merge_models ..).mp valid).2)
    ⟨0,2⟩ (List.mem_singleton_self _) ⟨0,3⟩ (List.mem_singleton_self _) rfl

theorem distinct_nonpoint_merge_has_model :
    Models (merge mergeState (GeneralNominalDemandMerging.pointSite mergeFirst)
      (GeneralNominalDemandMerging.pointSite mergeLast)) finiteModel := by
  have raw : GeneralNominalState.Models GeneralNominalCanonicalSiteObstruction.state finiteModel := by
    apply (GeneralNominalState.extend_models ..).mpr
    refine ⟨?_,(GeneralNominalCaptureMerges.equations_exact finiteModel 0 (.var 1)).mpr
      ⟨subtype_refl _,subtype_refl _⟩⟩
    exact ((GeneralNominalState.extend_models GeneralNominalIntervalExamples.source [] _ finiteModel).mp finite_source_models).1
  have before : Models mergeState finiteModel := by
    refine ⟨raw,(by intro p member; cases member),?_⟩
    intro site member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> exact point_holds _ finiteModel
  apply (GeneralNominalSaturationState.merge_models ..).mpr
  refine ⟨before,(GeneralNominalDemandMerging.output_atoms_exact _ _ _).mpr ?_⟩
  intro a ha b hb _
  have one := List.mem_singleton.mp ha; have two := List.mem_singleton.mp hb
  subst a; subst b
  exact ⟨subtype_refl _,subtype_refl _⟩

end Yulang.GeneralNominalFeedbackRegressions
