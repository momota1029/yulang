import Yulang.GeneralDictionaryAllocDefaultLocal202
import Yulang.GeneralDictionarySelectedInterface202
import Yulang.GeneralNominalCenteredHeadAllocV7Boundary
import Yulang.GeneralDictionaryLinearLeaf

set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralDictionaryAllocDefaultCounterexample202
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralNominalCenters GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open CommonNominalFullCarrier
open GeneralDictionaryAllocDefaultSource202
open GeneralDictionaryAllocDefaultLocal202
open GeneralNominalCenteredHeadMatStepKernel

theorem request_exact (member : output ∈ GeneralNominalCenteredHeadOutputs.requests start.core root) :
    output = ⟨0,1⟩ := by
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
      exact GeneralNominalCenteredTerminalForkSource.scalar assignment valid 1 (by decide +kernel)
    · intro entry member; cases member

theorem class_effects (assignment : GeneralNominalCommonBridge.Assignment) :
    GeneralNominalCenteredHeadMatEffects.ClassEffects start.core root plan assignment := by
  constructor
  · intro output member body found
    cases request_exact member
    have same : body = .default 0 0 (.var 0) := Option.some.inj found.symm
    subst body
    exact (GeneralNominalCenteredHeadMatEffects.positional_default plan assignment (0 : Fin 1)).mpr
      ⟨subtype_refl _,subtype_refl _⟩
  · intro first one last two _
    cases request_exact one
    cases request_exact two
    exact ⟨subtype_refl _,subtype_refl _⟩

theorem total_packet (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalCenteredHeadMatStepJournal.Models start assignment) :
    GeneralNominalCenteredHeadMatStepPackets.Holds plan assignment :=
  GeneralDictionaryMatTerminalAssembly200.holds_of_head_class plan start.core
    (List.mem_singleton_self _) assignment (head_model_any assignment valid.1)
    (head_equations_any assignment valid.1) (class_effects assignment) rfl

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

theorem stable : Stable registry start root := by
  intro focus generated after action
  have same := generated_only_root focus generated
  cases action with
  | administrative action =>
    cases action with
    | enqueue linked absent => exact absent _ (List.mem_singleton_self _) same.symm
    | refresh context certificate source member unknown known =>
        exact unknown (GeneralNominalCenteredTerminalForkSource.all_known _ source member)
    | equate first last one two equal novel =>
        apply novel
        intro assignment sourceModels
        exact equal assignment ((GeneralNominalCenteredHeadMatStepJournal.point_initial_models
          (fun _ => rfl)).mpr sourceModels)
    | reobserve revision certificate improved =>
        exact GeneralNominalReobservationSteps.pointClosed_no_revision
          (GeneralNominalCenteredTerminalForkSource.point_closed false) revision improved
  | refresh focus context certificate source member unknown known =>
      exact unknown (GeneralNominalCenteredTerminalForkSource.all_known _ source member)
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
  fun conflict => conflict.2 ⟨model,inhabited,⟨children,unique⟩,plan,frame,ready,head_equations,class_effects model⟩

theorem selected : GeneralNominalCenteredHeadMatStepBoundary.Local registry start root (.selected 37 []) := by
  have chosen := unique
  rw [children_empty] at chosen
  exact .selected safe chosen clear

theorem no_instance (assignment : GeneralNominalCommonBridge.Assignment) (kids : List (Occurrence roles)) :
    ¬ GeneralDictionaryRecursiveEvidence.Instance registry context assignment root 37 kids := by
  rintro ⟨decl,visible,check,_,_,bounds,_,_,ready,_,_,_⟩
  cases List.mem_singleton.mp visible
  obtain ⟨equation,member,_⟩ := ready.1 ⟨0,1⟩ (List.mem_singleton_self _)
  cases member

theorem no_evidence : ¬ (GeneralNominalCenteredHeadMatStepBoundary.boundary roles).Evidence registry start model root (.node 37 []) := by
  intro evidence
  obtain ⟨kids,instanceRule,_⟩ := GeneralDictionaryRecursiveEvidence.evidence_node_elim
    registry context model root 37 [] evidence
  exact no_instance model kids instanceRule

theorem compiled_registry : GeneralNominalCenteredHeadAllocEncoding.registry registry = registry := rfl

theorem alloc_initial : (GeneralNominalCenteredHeadAllocBoundary.boundary roles).Initial registry root start :=
  initial_source

theorem alloc_reachable : B4TargetV6.Reachable (GeneralNominalCenteredHeadAllocBoundary.boundary roles) registry root start :=
  ⟨start,alloc_initial,.refl⟩

theorem alloc_selected : GeneralNominalCenteredHeadAllocBoundary.Local registry start root (.selected 37 []) := by
  apply GeneralNominalCenteredHeadAllocBoundary.local_iff.mpr
  rw [compiled_registry]
  exact selected

/-- Refutes the exact I34 selected-only target, not the withdrawn prior type. -/
theorem not_selected_evidenceNode :
    ¬ GeneralDictionarySelectedInterface202.SelectedEvidenceNode (GeneralNominalCenteredHeadAllocBoundary.boundary roles) := by
  intro node
  apply no_evidence
  have result := (GeneralDictionarySelectedInterface202.selected_iff _).mp node
    registry ⟨rfl,checked⟩ start root alloc_reachable model inhabited root 37 [] [] (Or.inl rfl)
    (show GeneralNominalCenteredHeadAllocBoundary.Stable registry start root from stable)
    (by intro child member; cases member) alloc_selected .nil
  exact result

theorem no_merged_conflict : ¬ GeneralNominalCenteredHeadAllocMergedConflict.MergedOutputConflict start root := by
  rintro ⟨⟨first,last,member,_,_⟩,_⟩
  cases member

theorem v7_selected : GeneralNominalCenteredHeadAllocV7Boundary.Local registry start root (.selected 37 []) :=
  .ordinary no_merged_conflict alloc_selected

/-- The integrated V7 selected-node field has the same explicit-body mismatch. -/
theorem not_v7_evidenceNode :
    ¬ B4SkeletonV7.EvidenceNode (GeneralNominalCenteredHeadAllocV7Boundary.boundary roles) := by
  intro node
  apply no_evidence
  exact node registry ⟨rfl,checked⟩ start root alloc_reachable model inhabited root 37 [] []
    (Or.inl rfl) stable (by intro child member; cases member) v7_selected .nil

/-- A closed bundle of the positive premises; the model is an actual assignment. -/
theorem selected_inhabited_stable :
    (GeneralNominalCenteredHeadAllocV7Boundary.boundary roles).Checked registry ∧
    (GeneralNominalCenteredHeadAllocV7Boundary.boundary roles).Initial registry root start ∧
    B4TargetV7.Reachable (GeneralNominalCenteredHeadAllocV7Boundary.boundary roles) registry root start ∧
    GeneralNominalCenteredHeadMatStepJournal.Models start model ∧
    GeneralNominalCenteredHeadAllocV7Boundary.Stable registry start root ∧
    GeneralNominalCenteredHeadAllocV7Boundary.Local registry start root (.selected 37 []) ∧
    ¬ (GeneralNominalCenteredHeadAllocV7Boundary.boundary roles).Evidence registry start model root (.node 37 []) :=
  ⟨⟨rfl,checked⟩,alloc_initial,alloc_reachable,inhabited,stable,v7_selected,no_evidence⟩

theorem actual_default :
    GeneralDictionaryAssociatedProvenance.lookup roles declaration 0 = some (.default 0 0 (.var 0)) ∧
    declaration.associated = [] ∧
    GeneralNominalCenteredHeadMatEffects.BodyHolds plan 1 model (.default 0 0 (.var 0)) ∧
    GeneralNominalCenteredHeadMatStepPackets.Holds plan model := by
  refine ⟨rfl,rfl,?_,total_packet model inhabited⟩
  exact (GeneralNominalCenteredHeadMatEffects.positional_default plan model (0 : Fin 1)).mpr
    ⟨subtype_refl _,subtype_refl _⟩

end Yulang.GeneralDictionaryAllocDefaultCounterexample202
