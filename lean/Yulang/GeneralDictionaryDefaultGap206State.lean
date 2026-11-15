import Yulang.GeneralNominalCenteredHeadAllocMergeStable
import Yulang.GeneralDictionaryDefaultGap206Local
import Yulang.GeneralDictionarySelectedInterface202
import Yulang.GeneralNominalCenteredHeadAllocV7Boundary
import Yulang.GeneralDictionaryLinearLeaf

set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralDictionaryDefaultGap206State
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralNominalCenters GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open CommonNominalFullCarrier
open GeneralDictionaryDefaultGap206Source
open GeneralDictionaryDefaultGap206Local
open GeneralNominalCenteredHeadMatStepKernel

theorem request_exact (member : output ∈ GeneralNominalCenteredHeadOutputs.requests start.core root) :
    output = ⟨0,0⟩ := by
  obtain ⟨site,present,_,within⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp member
  cases List.mem_singleton.mp present
  exact List.mem_singleton.mp within

theorem head_equations_any (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models snapshot assignment) :
    GeneralNominalCenteredHeadOutputs.HeadEquations plan assignment := by
  refine ⟨point_root_holds _ root (fun _ => rfl) assignment,?_,?_⟩
  · intro name member
    simp [Declaration.inputNames,normalizeArgs,normalize,variablesArgs,Pattern.variables] at member
  · rw [head_schema]
    constructor
    · intro test member
      cases List.mem_singleton.mp member
      refine ⟨⟨_,.source _⟩,?_⟩
      intro actual seen
      cases seen
      exact scalar assignment valid
    · intro entry member; cases member

theorem class_effects :
    GeneralNominalCenteredHeadMatEffects.ClassEffects start.core root plan model := by
  constructor
  · intro output member body found
    cases request_exact member
    have same : body = .default 0 0 (.var 0) := Option.some.inj found.symm
    subst body
    exact (GeneralNominalCenteredHeadMatEffects.positional_default plan model (0 : Fin 1)).mpr
      ⟨subtype_refl _,subtype_refl _⟩
  · intro first one last two _
    cases request_exact one
    cases request_exact two
    exact ⟨subtype_refl _,subtype_refl _⟩

theorem total_packet (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalCenteredHeadMatStepJournal.Models start assignment) :
    GeneralNominalCenteredHeadMatStepPackets.Holds plan assignment :=
by
  have hm := head_model_any assignment valid.1
  have he := head_equations_any assignment valid.1
  have privateModels : GeneralNominalState.Models plan.packet.privateContext.state assignment := hm.1
  have base := (GeneralNominalPacketSupport.private_exact plan.packet assignment).mp privateModels
  have outputs : GeneralNominalCenteredHeadMatStepPackets.Outputs plan assignment := by
    unfold GeneralNominalCenteredHeadMatStepPackets.Outputs GeneralNominalCenteredHeadMatPlans.emittedSchema
    rw [GeneralDictionaryMatTerminalAssembly200.terminal_requests plan rfl]
    change (GeneralNominalCenteredHeadMatSchemas.generated _ _ []).Holds _ _
    intro equation member; cases member
  refine ⟨base.1,⟨base.2,hm.2,he.1,?_,he.2.2,?_,?_⟩,outputs⟩
  · intro name member
    rcases member with member | ⟨clause,member,_⟩
    · exact he.2.1 name member
    · cases member
  · intro equation member _; exact outputs equation member
  · intro clause member; cases member

theorem children_empty : children = [] :=
  GeneralDictionaryLinearLeaf.children_empty context registry root declaration declaration_checked rfl _

theorem committed : Committed start plan :=
  ⟨total_packet,by intro child member; change child ∈ children at member; rw [children_empty] at member; cases member⟩

theorem generated_only_root (focus : Occurrence roles)
    (generated : GeneralNominalSaturationState.Generated start.core.erased.current root focus) : focus = root := by
  induction generated with
  | root => rfl
  | child prior member ih => cases member
  | alias prior one two same ih =>
    exact congrArg GeneralNominalDemandMerging.Site.occurrence (List.mem_singleton.mp two)

theorem counter_inhabited : GeneralNominalCenteredHeadMatStepJournal.Models start counter :=
  (GeneralNominalCenteredHeadMatStepJournal.point_initial_models (fun _ => rfl)).mpr counter_model

theorem no_refresh (certificate : GeneralNominalCenteredHeadMatStepRefresh.Refresh start nextContext)
    (unknown : ¬ GeneralNominalState.Known snapshot identity)
    (known : GeneralNominalState.Known nextContext.state identity) : False := by
  have neone : identity ≠ 1 := by
    rintro rfl; exact unknown ⟨(1 : Fin 3),rfl,Or.inl (by decide +kernel)⟩
  have netwo : identity ≠ 2 := by
    rintro rfl; exact unknown ⟨(2 : Fin 3),rfl,Or.inl (by decide +kernel)⟩
  obtain ⟨test,observation,head⟩ := GeneralNominalCenteredHeadMatStepCache.known_has_head known
  have valid := GeneralNominalCenteredHeadAllocMergeStable.head_holds head
    (GeneralNominalCenteredHeadMatStepObservations.cache_sound certificate.cache
      (GeneralNominalSupport.head_recorded head) counter_inhabited)
  have bottom : (counter identity).1 = .bottom := by simp [neone,netwo]
  rw [bottom] at valid
  exact GeneralNominalCenteredHeadMatHeadShape.bottom_no_head test valid

theorem stable : Stable registry start root := by
  intro focus generated after action
  have same := generated_only_root focus generated
  cases action with
  | administrative action =>
    cases action with
    | enqueue linked absent => exact absent _ (List.mem_singleton_self _) same.symm
    | refresh context certificate source _member unknown known =>
        exact no_refresh certificate unknown known
    | equate first last one two equal novel =>
        apply novel
        intro assignment sourceModels
        exact equal assignment ((GeneralNominalCenteredHeadMatStepJournal.point_initial_models
          (fun _ => rfl)).mpr sourceModels)
    | reobserve revision certificate improved =>
        exact GeneralNominalReobservationSteps.pointClosed_no_revision
          (by intro slot descriptor recorded; cases recorded) revision improved
  | refresh focus context certificate source _member unknown known =>
      exact no_refresh certificate unknown known
  | install candidate enabled novel =>
      have framed := same ▸ enabled.snapshot_eq ▸ enabled.registry_eq ▸ candidate.frame
      have planEq := frame_plan framed
      exact novel (planEq.symm ▸ committed)
  | merge first last one two inputs novel =>
    have a := List.mem_singleton.mp one
    have b := List.mem_singleton.mp two
    subst first; subst last
    exact novel (.refl _)

theorem ready : GeneralNominalCenteredHeadMatEffects.Ready start.core root plan :=
  GeneralNominalCenteredHeadMatEffects.ready_of_wf coverage (List.mem_singleton_self _) rfl (by
    intro output member
    cases request_exact member
    exact ⟨some (.var 0),rfl⟩)

theorem clear : ¬ (GeneralNominalCenteredHeadMatStepBoundary.boundary roles).OutputConflict registry start root 37 :=
  fun conflict => conflict.2 ⟨model,inhabited,⟨children,unique⟩,plan,frame,ready,head_equations,class_effects⟩

theorem selected : GeneralNominalCenteredHeadMatStepBoundary.Local registry start root (.selected 37 []) := by
  have chosen := unique
  rw [children_empty] at chosen
  exact .selected safe chosen clear

theorem compiled_registry : GeneralNominalCenteredHeadAllocEncoding.registry registry = registry := rfl

theorem alloc_initial : (GeneralNominalCenteredHeadAllocBoundary.boundary roles).Initial registry root start :=
  initial_source

theorem alloc_reachable : B4TargetV6.Reachable (GeneralNominalCenteredHeadAllocBoundary.boundary roles) registry root start :=
  ⟨start,alloc_initial,.refl⟩

theorem alloc_selected : GeneralNominalCenteredHeadAllocBoundary.Local registry start root (.selected 37 []) := by
  apply GeneralNominalCenteredHeadAllocBoundary.local_iff.mpr
  rw [compiled_registry]
  exact selected

theorem no_merged_conflict : ¬ GeneralNominalCenteredHeadAllocMergedConflict.MergedOutputConflict start root := by
  rintro ⟨⟨first,last,member,_,_⟩,_⟩
  cases member

theorem v7_selected : GeneralNominalCenteredHeadAllocV7Boundary.Local registry start root (.selected 37 []) :=
  .ordinary no_merged_conflict alloc_selected


end Yulang.GeneralDictionaryDefaultGap206State
