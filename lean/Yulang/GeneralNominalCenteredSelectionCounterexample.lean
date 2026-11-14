import Yulang.GeneralNominalCenteredPointMergeExample
import Yulang.GeneralNominalCenteredInspection
import Yulang.GeneralNominalCenteredGroundBoundary
import Yulang.GeneralNominalCenteredWhere
import Yulang.GeneralDictionaryEarlyMergeScalarJoint
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalCenteredSelectionCounterexample
open GeneralDictionaryEarlyMergeScalarExample
private theorem alias_cycle (state : GeneralNominalSaturationState.State roles) (aliases) (source) :
    GeneralNominalFeedbackK2.Cycle {state with aliases := aliases} source ↔
    GeneralNominalFeedbackK2.Cycle state source := by
  have paths (a b) : GeneralNominalFeedbackK2.Path {state with aliases := aliases} a b ↔
      GeneralNominalFeedbackK2.Path state a b := by
    constructor <;> intro path <;> induction path with
    | nil => exact .nil _
    | cons edge tail ih => exact .cons edge ih
  constructor <;> rintro ⟨next,edge,path⟩
  · exact ⟨next,edge,(paths _ _).mp path⟩
  · exact ⟨next,edge,(paths _ _).mpr path⟩
private theorem alias_root (state : GeneralNominalSaturationState.State roles) (aliases) (root) :
    GeneralNominalFeedbackK2.RootK2 {state with aliases := aliases} root ↔
    GeneralNominalFeedbackK2.RootK2 state root := by
  simp only [GeneralNominalFeedbackK2.RootK2,GeneralNominalFeedbackK2.RecursAt,alias_cycle]
  rfl
private theorem alias_candidate (state : GeneralNominalSaturationState.State roles) (aliases) (registry root) :
    GeneralNominalFeedbackK2.CandidateK2 registry {state with aliases := aliases} root ↔
    GeneralNominalFeedbackK2.CandidateK2 registry state root := by
  simp only [GeneralNominalFeedbackK2.CandidateK2,GeneralNominalFeedbackK2.RecursAt,alias_cycle]
  rfl
private theorem alias_selected (state : GeneralNominalSaturationState.State roles) (aliases)
    (children : List (GeneralSourceDictionaries.Occurrence roles))
    (selected : GeneralNominalFeedbackK2.Local registry {state with aliases := aliases} root (.selected key children)) :
    GeneralNominalFeedbackK2.Local registry state root (.selected key children) := by
  cases selected with
  | selected safe unique =>
    exact .selected ⟨safe.1,fun h => safe.2.1 ((alias_root _ _ _).mpr h),
      fun h => safe.2.2.1 ((alias_candidate _ _ _ _).mpr h),safe.2.2.2⟩ unique
private theorem finish_shape : finish.current =
    {before.current with aliases := ((child 10).identity,(child 11).identity) :: before.current.aliases} := by
  have empty : GeneralNominalDemandMerging.outputAtoms (site 10) (site 11) = [] := rfl
  unfold finish GeneralNominalSupportSteps.merge GeneralNominalSaturationState.merge
  simp only [empty,GeneralNominalState.extend,List.append_nil]
  rfl
theorem premerge_selected (n : Nat) : GeneralNominalFeedbackK2.Local registry before.current (child n) (.selected 3 []) := by
  have h := GeneralDictionaryEarlyMergeScalarClassification.child_selected n
  rw [finish_shape] at h
  exact alias_selected _ _ _ h
theorem premerge_not_closed : ¬ GeneralNominalFeedbackSteps.MergesClosed before.current (site 10) := by
  intro closed
  have alias := closed (site 11) (site_present 11 (Or.inr rfl)) inputs_same
  have eq_of_alias : ∀ a b, GeneralNominalSaturationState.Alias before.current a b → a=b := by
    intro a b h
    induction h with
    | refl => rfl
    | edge member => cases member
    | symm h ih => exact ih.symm
    | trans one two ih₁ ih₂ => exact ih₁.trans ih₂
  exact GeneralDictionaryEarlyMergeScalarJoint.distinct_children (eq_of_alias _ _ alias)
open GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralNominalExamples (context state displayRoot model state_models)
open GeneralDeclarationExamples (roles)
abbrev cstart := GeneralNominalCenteredSteps.initial (context true) displayRoot
abbrev cplan : Plan roles := ⟨packet,rootSite (state true).seed displayRoot,rfl⟩
noncomputable abbrev cbefore := GeneralNominalCenteredSteps.install cstart cplan []
theorem cequations (m : GeneralNominalCommonBridge.Assignment) (valid : GeneralNominalState.Models (state true) m) :
    cplan.Equations m :=
  GeneralNominalCenteredPointMergeExample.equations m valid
theorem cselected : GeneralNominalCenteredBoundary.Local registry cstart displayRoot (.selected 1 children) := by
  apply GeneralNominalCenteredBoundary.selected_of_old (GeneralNominalSupportBoundary.selected_old selected)
  · exact GeneralNominalCenteredPointMergeExample.initial_acyclic
  · exact GeneralNominalCenteredSupport.legacy_decision
      (GeneralNominalSharedPositive.initial_decision _ _ _ _ [] (all_source_decisions displayRoot (fun _ => rfl)))
theorem cguard : PacketGuard cstart cplan [] := by
  apply (GeneralNominalCenteredInspection.selected_guard_reduction cplan cselected enabled (List.mem_singleton_self _) []).mpr
  exact ⟨GeneralNominalValueSupport.source_packet _ _ packet_guard,
    model,(point_initial_models _ _ (fun _ => rfl) model).mpr (state_models true),
    branch model (state_models true),cequations model (state_models true)⟩
theorem cfirst : Step registry displayRoot cstart cbefore :=
  ⟨displayRoot,.root,.install cplan [] enabled novel cguard⟩
theorem csource : InitialSource registry displayRoot cstart :=
  GeneralNominalCenteredSteps.initial_source source




open CommonNominalFullCarrier GeneralNominalOriginTerms
open GeneralNominalRecursiveInspection

private theorem cbefore_model : Models cbefore model :=
  (GeneralNominalCenteredSteps.install_models (plan := cplan) (state := cstart) (support := []) rfl model).mpr
    ⟨(point_initial_models _ _ (fun _ => rfl) model).mpr (state_models true),
      branch model (state_models true),cequations model (state_models true)⟩

private def height (source : Nat) : Nat := if source = 0 then 1 else 0
private theorem model_height (source : Nat) : (model source).1 = GeneralNominalOutputGrowth.tower (height source) := by
  by_cases zero : source = 0 <;> simp [height,zero,GeneralNominalOutputGrowth.tower] <;> rfl

private theorem feedback_acyclic (source : Nat) :
    ¬ GeneralNominalFeedbackK2.Cycle cbefore.erased.current source :=
  GeneralNominalOutputGrowthModels.feedback_acyclic _ model cbefore_model.1 height model_height
    (by rintro _ _ ⟨_,_,⟨kind,_,_,_⟩,_,_⟩; exact Fin.elim0 kind) source

private theorem graph_tests : (graph cbefore).tests = [(.source 0,.nominal 0 1)] := by
  change GeneralNominalCenteredSteps.Plan.tests cplan ++ [] = _
  rw [List.append_nil]
  change GeneralNominalCenteredSteps.Plan.tests GeneralNominalCenteredPointMergeExample.plan = _
  unfold GeneralNominalCenteredSteps.Plan.tests
  rw [GeneralNominalCenteredPointMergeExample.head_schema,GeneralNominalCenteredPointMergeExample.named_empty]
  simp [GeneralNominalCenters.Plan.schema,GeneralNominalCenters.Plan.childRequests,
    List.ofFn_succ,GeneralNominalMaterialization.generated,GeneralNominalMaterialization.schema,
    GeneralNominalMaterialization.Schema.append,GeneralNominalInspection.translate,GeneralDeclarationPatterns.normalize]

private theorem center_distinct : ¬ Same model (.source 0) (.source 1) := by
  intro same
  have equal := same.2.2 _ _ (.source 0) (.source 1)
  have impossible : 1 = 0 := (GeneralNominalOutputGrowth.tower_equivalent 1 0).mp equal
  cases impossible

private theorem recorded_shapes (recorded : GeneralNominalCenteredGraph.Recorded (graph cbefore) first last) :
    Same model first (.source 0) ∧ Same model last (.source 1) := by
  cases recorded with
  | structural shape index member => rw [graph_tests] at member; cases List.mem_singleton.mp member
  | nominal name arity index member =>
    rw [graph_tests] at member
    cases List.mem_singleton.mp member
    have zero : index.val = 0 := by omega
    rw [zero]
    refine ⟨source_self model 0,?_⟩
    have equations := cequations model (state_models true)
    have actual := equations.2.2.1.2
    rw [show cplan.headSchema = GeneralNominalCenteredPointMergeExample.plan.headSchema from rfl,
      GeneralNominalCenteredPointMergeExample.head_schema] at actual
    have same := actual ⟨0,.nominal (.source 0) 0 0,.actual⟩ (by simp)
    simpa only [ite_true,show cplan.binder 0 = 1 from GeneralNominalCenteredPointMergeExample.binder_zero] using same

private theorem graph_acyclic (origin : Origin) : ¬ GeneralNominalCenteredGraph.Cyclic (graph cbefore) origin := by
  have endpoints {first last} (edge : GeneralNominalCenteredGraph.Edge (graph cbefore) first last) :
      Same model first (.source 0) ∧ Same model last (.source 1) := by
    obtain ⟨parent,child,recorded,left,right⟩ := edge
    have shape := recorded_shapes recorded
    exact ⟨same_trans (left model cbefore_model) shape.1,
      same_trans (same_symm (right model cbefore_model)) shape.2⟩
  rintro ⟨⟨next,edge,path⟩,_⟩
  have one := endpoints edge
  cases path with
  | nil => exact center_distinct (same_trans (same_symm one.1) one.2)
  | cons edge rest =>
    have two := endpoints edge
    exact center_distinct (same_trans (same_symm two.1) one.2)

private theorem centered_acyclic (origin : Origin) : ¬ Cyclic cbefore origin := by
  rintro (⟨source,_,cycle,_⟩ | cycle)
  · exact feedback_acyclic source cycle
  · exact graph_acyclic origin cycle

private theorem child_old_selected (n : Nat) :
    GeneralNominalFeedbackK2.Local registry cbefore.erased.current (child n) (.selected 3 []) := by
  cases premerge_selected n with
  | selected safe unique =>
    refine .selected ⟨safe.1,?_,?_,safe.2.2.2⟩ unique
    · rintro (old | ⟨_,_,_,cycle,_⟩)
      · exact safe.2.1 (Or.inl old)
      · exact feedback_acyclic _ cycle
    · rintro (old | ⟨_,_,_,_,_,_,_,_,_,_,cycle,_⟩)
      · exact safe.2.2.1 (Or.inl old)
      · exact feedback_acyclic _ cycle

private theorem source_ready (slot : Fin 2) :
    GeneralNominalSharedSupport.ReadyAt cbefore.erased slot.val := by
  have bounded := slot.isLt
  by_cases zero : slot.val = 0
  · have same : slot = 0 := Fin.ext zero
    subst slot
    exact ⟨_,_,GeneralNominalSupport.Head.nominal (snapshot := cbefore.erased.current.context.state) (0 : Fin 2) GeneralNominalExamples.listDescriptor rfl,
      GeneralNominalSharedSupport.source_head _ (GeneralNominalSupport.Head.nominal (snapshot := state true) 0 GeneralNominalExamples.listDescriptor rfl)⟩
  · have same : slot = 1 := by apply Fin.ext; omega
    subst slot
    exact ⟨_,_,GeneralNominalSupport.Head.scalar (snapshot := cbefore.erased.current.context.state) (1 : Fin 2) .int rfl,
      GeneralNominalSharedSupport.source_head _ (GeneralNominalSupport.Head.scalar (snapshot := state true) 1 .int rfl)⟩

theorem child_selected (n : Nat) :
    GeneralNominalCenteredBoundary.Local registry cbefore (child n) (.selected 3 []) := by
  apply GeneralNominalCenteredBoundary.selected_of_old (child_old_selected n) centered_acyclic
  apply GeneralNominalCenteredSupport.legacy_decision
  exact ⟨fun _ => source_ready 1,fun _ _ _ _ _ slot _ => source_ready slot⟩


private theorem raw_sites : cbefore.erased.current.sites =
    [GeneralNominalDemandMerging.pointSite displayRoot,
      GeneralNominalCenteredPointMergeExample.rawSite 10,GeneralNominalCenteredPointMergeExample.rawSite 11] :=
  GeneralNominalCenteredPointMergeExample.raw_sites

private theorem no_alias {first last : Nat}
    (alias : GeneralNominalSaturationState.Alias cbefore.erased.current first last) : first = last := by
  induction alias with
  | refl => rfl
  | edge member => cases member
  | symm _ ih => exact ih.symm
  | trans _ _ first last => exact first.trans last

private theorem raw_same : GeneralNominalFeedbackSites.SameInputs cbefore.erased.current
    (GeneralNominalCenteredPointMergeExample.rawSite 10) (GeneralNominalCenteredPointMergeExample.rawSite 11) := by
  apply GeneralDictionaryFeedbackEvidence.sameInputs_recovered
  refine ⟨rfl,?_⟩
  rw [GeneralNominalCenteredPointMergeExample.raw_inputs 10 (Or.inl rfl),
    GeneralNominalCenteredPointMergeExample.raw_inputs 11 (Or.inr rfl)]
  refine .cons ⟨_,_,rfl,rfl,?_⟩ .nil
  intro m valid
  have source := (GeneralNominalSharedSteps.install_models (state := cstart.erased) (packet := packet)
    (support := []) rfl m).mp valid |>.1.1
  have equations := cequations m source
  have head := equations.2.2.1
  rw [show cplan.headSchema = GeneralNominalCenteredPointMergeExample.plan.headSchema from rfl,
    GeneralNominalCenteredPointMergeExample.head_schema] at head
  have same := head.2 ⟨0,GeneralNominalCenteredPointMergeExample.origin,.actual⟩ (by simp)
  simp only [ite_true] at same
  exact same_trans same (same_symm same)

theorem child_not_installable (plan : Plan roles) (focus : plan.packet.site.occurrence = child 10) :
    ¬ GeneralNominalCenteredBoundary.Installable registry cbefore plan := by
  intro enabled
  have present := enabled.1.1.2.2.1
  rw [raw_sites] at present
  simp only [List.mem_cons,List.not_mem_nil,or_false] at present
  rcases present with same | same | same
  · have incompatible := (congrArg (fun s : GeneralNominalDemandMerging.Site roles => s.occurrence) same).symm.trans focus
    change displayRoot = child 10 at incompatible
    have impossible := congrArg GeneralSourceDictionaries.Occurrence.identity incompatible
    contradiction
  · have other : GeneralNominalCenteredPointMergeExample.rawSite 11 ∈ cbefore.erased.current.sites := by
      rw [raw_sites]; simp
    have alias := enabled.1.2.2 _ other (by simpa only [same] using raw_same)
    have equal := no_alias alias
    rw [focus] at equal
    exact GeneralDictionaryEarlyMergeScalarJoint.distinct_children equal
  · have incompatible := (congrArg (fun s : GeneralNominalDemandMerging.Site roles => s.occurrence) same).symm.trans focus
    change child 11 = child 10 at incompatible
    exact GeneralDictionaryEarlyMergeScalarJoint.distinct_children
      (congrArg GeneralSourceDictionaries.Occurrence.identity incompatible).symm


theorem ground_reachable : B4TargetV5.Reachable
    (GeneralNominalCenteredGroundBoundary.groundBoundary roles) registry displayRoot cbefore :=
  ⟨cstart,⟨context true,[.app 0 [.app 2 []]],source,(fun _ => rfl),
    GeneralNominalCenteredPointMergeExample.ground,rfl⟩,.tail .refl cfirst⟩

theorem child_generated : GeneralNominalSaturationState.Generated cbefore.erased.current displayRoot (child 10) := by
  apply GeneralNominalSaturationState.Generated.child .root
  change (displayRoot,child 10) ∈ [] ++ packet.children.map (fun c => (displayRoot,c))
  apply List.mem_append_right
  apply List.mem_map.mpr
  refine ⟨child 10,?_,rfl⟩
  change child 10 ∈ children
  rw [children_exact]
  simp

theorem not_available : ¬ GeneralNominalCenteredWhere.Available registry cbefore (child 10) := by
  intro available
  obtain ⟨plan,focus,enabled⟩ := available 3 [] (child_selected 10)
  exact child_not_installable plan focus enabled

theorem required_merge_step : Step registry displayRoot cbefore
    (GeneralNominalCenteredSteps.merge cbefore
      (GeneralNominalCenteredPointMergeExample.centerSite 10)
      (GeneralNominalCenteredPointMergeExample.centerSite 11) []) := by
  have centers : cbefore.sites =
      [cplan.input,GeneralNominalCenteredPointMergeExample.centerSite 10,
        GeneralNominalCenteredPointMergeExample.centerSite 11] :=
    GeneralNominalCenteredPointMergeExample.center_sites
  refine ⟨child 10,child_generated,.merge
    (GeneralNominalCenteredPointMergeExample.centerSite 10)
    (GeneralNominalCenteredPointMergeExample.centerSite 11) [] ?_ ?_ ?_ ?_ ?_⟩
  · rw [centers]; simp
  · rw [centers]; simp
  · exact ⟨rfl,.cons ⟨_,_,rfl,rfl,GeneralNominalDemandMerging.source_same _ 1⟩ .nil⟩
  · exact fun alias => GeneralDictionaryEarlyMergeScalarJoint.distinct_children (no_alias alias)
  · refine ⟨⟨rfl,.cons ⟨_,_,rfl,rfl,GeneralNominalDemandMerging.source_same _ 1⟩ .nil⟩,?_,?_⟩
    all_goals
      intro index absent
      have zero : index.val = 0 := by have bound := index.isLt; change index.val < 1 at bound; omega
      rw [GeneralNominalCenteredPointMergeExample.center_inputs,zero] at absent
      cases absent

theorem reachable_selected_obstruction :
    GeneralDeclarations.Checked registry ∧
    B4TargetV5.Reachable (GeneralNominalCenteredGroundBoundary.groundBoundary roles) registry displayRoot cbefore ∧
    GeneralNominalSaturationState.Generated cbefore.erased.current displayRoot (child 10) ∧
    GeneralNominalCenteredBoundary.Local registry cbefore (child 10) (.selected 3 []) ∧
    ¬ ∃ plan : Plan roles, plan.packet.site.occurrence = child 10 ∧
      GeneralNominalCenteredBoundary.Installable registry cbefore plan :=
  ⟨registry_checked,ground_reachable,child_generated,child_selected 10,
    fun ⟨plan,focus,enabled⟩ => child_not_installable plan focus enabled⟩

end Yulang.GeneralNominalCenteredSelectionCounterexample
