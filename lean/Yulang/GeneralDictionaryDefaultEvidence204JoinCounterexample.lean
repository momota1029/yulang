import Yulang.GeneralDictionaryDefaultEvidence204JoinLocal
import Yulang.GeneralDictionarySelectedInterface202
import Yulang.GeneralNominalCenteredHeadAllocV7Boundary
import Yulang.GeneralDictionaryLinearLeaf
import Yulang.GeneralDictionaryDefaultBoundary204

set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralDictionaryDefaultEvidence204JoinCounterexample
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralNominalCenters GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open CommonNominalFullCarrier
open GeneralDictionaryDefaultEvidence204JoinSource
open GeneralDictionaryDefaultEvidence204JoinLocal
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

theorem union_self (type : Ty) : Equivalent type (.union type type) :=
  ⟨fun _ => CommonNominalFullDemand.producerLe_union_left _ _,
    fun _ => (CommonNominalFullDemand.producerLe_union_iff _ _ _).mpr
      ⟨CommonNominalFullDemand.producerLe_refl _,CommonNominalFullDemand.producerLe_refl _⟩⟩

theorem class_effects (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models snapshot assignment) :
    GeneralNominalCenteredHeadMatEffects.ClassEffects start.core root plan assignment := by
  constructor
  · intro output member body found
    cases request_exact member
    have same : body = .explicit equation := Option.some.inj found.symm
    subst body
    apply (GeneralNominalCenteredHeadMatEffects.body_equation (show
      GeneralNominalCenteredHeadMatEffects.compileBody plan (.explicit equation) =
        some (.join (.primitive (.scalar .int) []) (.primitive (.scalar .int) [])) from rfl)).mpr
    have scalar := GeneralNominalCenteredTerminalForkSource.scalar assignment valid 1 (by decide +kernel)
    have joined := union_self (.base .int)
    exact ⟨subtype_trans scalar.1 joined.1,subtype_trans joined.2 scalar.2⟩
  · intro first one last two _
    cases request_exact one
    cases request_exact two
    exact ⟨subtype_refl _,subtype_refl _⟩

theorem total_packet (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalCenteredHeadMatStepJournal.Models start assignment) :
    GeneralNominalCenteredHeadMatStepPackets.Holds plan assignment :=
  GeneralDictionaryMatTerminalAssembly200.holds_of_head_class plan start.core
    (List.mem_singleton_self _) assignment (head_model_any assignment valid.1)
    (head_equations_any assignment valid.1) (class_effects assignment valid.1) rfl

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
  fun conflict => conflict.2 ⟨model,inhabited,⟨children,unique⟩,plan,frame,ready,head_equations,class_effects model source_model⟩

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

theorem generated_unknown : (generated registry context root declaration declaration_checked [(1,1)]).unknown = true := by
  unfold generated
  rw [GeneralNominalFiniteAssociatedFacts.terminal_requests context.state registry root declaration declaration_checked _ rfl]
  simp [GeneralNominalMaterialization.rootRequests,GeneralNominalMaterialization.generated,
    GeneralNominalMaterialization.schema,GeneralNominalMaterialization.Schema.append,
    equation,normalize,merge,variantRow,GeneralNominalInspection.translate]

/-- The obstruction predates the default extension: an explicitly defined
output is rejected by the inherited partial-materialization readiness guard. -/
theorem no_legacy_instance (assignment : GeneralNominalCommonBridge.Assignment)
    (kids : List (Occurrence roles)) :
    ¬ GeneralDictionaryRecursiveEvidence.Instance registry context assignment root 37 kids := by
  rintro ⟨decl,visible,check,_,_,bounds,located,_,ready,_⟩
  cases List.mem_singleton.mp visible
  have boundsEq : [(1,1)] = bounds := Option.some.inj located
  subst bounds
  have impossible := ready.2
  rw [generated_unknown] at impossible
  cases impossible

theorem no_instance (assignment : GeneralNominalCommonBridge.Assignment) (kids : List (Occurrence roles)) :
    ¬ GeneralDictionaryDefaultEvidence204.Instance registry start.core assignment root 37 kids := by
  rintro ⟨candidate,certificate⟩
  rcases candidate with ⟨⟨reg,ctx,site,decl,check,bounds⟩,input,inputEq⟩
  have regEq : reg = registry := certificate.registry_eq
  have ctxEq : ctx = context := certificate.context_eq
  have declEq : decl = declaration := List.mem_singleton.mp certificate.visible
  subst reg; subst ctx; subst decl
  have boundsEq : [(1,1)] = bounds := Option.some.inj certificate.located
  subst bounds
  have rootEq : site.occurrence = root := certificate.root_eq
  have ready := certificate.generated_ready
  change (generated registry context site.occurrence declaration declaration_checked [(1,1)]).unknown = false at ready
  rw [rootEq,generated_unknown] at ready
  cases ready

theorem no_evidence : ¬ GeneralDictionaryDefaultEvidence204.Evidence registry start.core model root (.node 37 []) := by
  intro evidence
  obtain ⟨kids,source,_⟩ := GeneralDictionaryDefaultEvidence204.evidence_node_elim evidence
  exact no_instance model kids source

theorem not_evidenceNode : ¬ B4SkeletonV7.EvidenceNode (GeneralDictionaryDefaultBoundary204.boundary roles) := by
  intro node
  apply no_evidence
  exact node registry ⟨rfl,checked⟩ start root alloc_reachable model inhabited root 37 [] []
    (Or.inl rfl) stable (by intro child member; cases member)
    (GeneralDictionaryDefaultBoundary204.local_iff.mpr v7_selected) .nil

/-- Every positive premise of the exact successor node field has a closed witness.
This uses the boundary-permitted compatible primitive aliases 2 and 42. -/
theorem positive_premises :
    (GeneralDictionaryDefaultBoundary204.boundary roles).Checked registry ∧
    (GeneralDictionaryDefaultBoundary204.boundary roles).Initial registry root start ∧
    B4TargetV7.Reachable (GeneralDictionaryDefaultBoundary204.boundary roles) registry root start ∧
    (GeneralDictionaryDefaultBoundary204.boundary roles).Models start model ∧
    (GeneralDictionaryDefaultBoundary204.boundary roles).Stable registry start root ∧
    B4TargetV7.Local (GeneralDictionaryDefaultBoundary204.boundary roles) registry start root (.selected 37 []) ∧
    CommonRoleOutermostResolver.All₂
      (fun child dictionary => (GeneralDictionaryDefaultBoundary204.boundary roles).Evidence registry start model child dictionary)
      [] [] :=
  ⟨⟨rfl,checked⟩,alloc_initial,alloc_reachable,inhabited,stable,
    GeneralDictionaryDefaultBoundary204.local_iff.mpr v7_selected,.nil⟩

/-- The total translator and body semantics succeed; the retained partial
request compiler, not absence of source meaning, rejects the evidence. -/
theorem total_vs_partial :
    GeneralNominalCenteredHeadMatEffects.compileBody plan (.explicit equation) =
      some (.join (.primitive (.scalar .int) []) (.primitive (.scalar .int) [])) ∧
    GeneralNominalCenteredHeadMatEffects.BodyHolds plan 1 model (.explicit equation) ∧
    GeneralNominalCenteredHeadMatStepPackets.Holds plan model ∧
    (generated registry context root declaration declaration_checked [(1,1)]).unknown = true := by
  refine ⟨rfl,?_,total_packet model inhabited,generated_unknown⟩
  exact (class_effects model source_model).1 ⟨0,1⟩
    (GeneralNominalCenteredHeadOutputs.request_retained _ (List.mem_singleton_self _) (.refl _) (List.mem_singleton_self _))
    (.explicit equation) rfl

end Yulang.GeneralDictionaryDefaultEvidence204JoinCounterexample
