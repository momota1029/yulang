import Yulang.GeneralNominalTwoHeadFixture190
import Yulang.GeneralNominalSourceLinearEvidence190
import Yulang.GeneralNominalCenteredHeadWFJoinCounterexample

set_option backward.isDefEq.respectTransparency false

/-! Nonvacuous actual head selection for the reused scalar leaf fixture. -/
namespace Yulang.GeneralNominalTwoHeadNonvacuity190
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralNominalCenters GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralNominalCenteredHeadOutputs CommonNominalFullCarrier
open GeneralNominalTwoHeadFixture190

theorem known : ¬ GeneralNominalState.RootPending snapshot root.demand := by
  rintro ⟨index,unknown⟩
  exact unknown ⟨(1 : Fin 3),rfl,Or.inl (by decide +kernel)⟩

theorem survivor : GeneralNominalCenteredHeadCandidates.Survivor registry context root 3 children :=
  ⟨known,declaration,List.mem_singleton_self _,declaration_checked,rfl,rfl,[(1,1),(1,1)],rfl,prepared,rfl⟩

theorem unique : GeneralNominalCenteredHeadCandidates.Unique registry context root 3 children := by
  refine ⟨survivor,?_⟩
  intro key kids found
  have copy := found
  obtain ⟨_,d,visible,_,identity,_⟩ := found
  cases List.mem_singleton.mp visible
  have same : key = 3 := identity.symm
  subst key
  exact ⟨rfl,GeneralNominalCenteredHeadCandidates.survivor_children_functional checked copy survivor⟩

theorem frame : Frame registry start.core root 3 plan :=
  ⟨rfl,rfl,rfl,rfl,List.mem_singleton_self _,List.mem_singleton_self _,List.mem_singleton_self _,rfl,rfl,prepared⟩

theorem requests_exact : requests start.core root = [⟨0,1⟩] :=
  GeneralNominalHeadInitialEffects188.initial_requests context

theorem capture_names (name : Nat) (member : name ∈ [0,1]) :
    (GeneralNominalPacketSupport.capture plan.packet).inputs name = (1,1) := by
  unfold GeneralNominalPacketSupport.capture
  have b : packet.bindings = [(0,1,1),(1,1,1)] := by
    change bindings snapshot (report context declaration [(1,1),(1,1)]) = _
    rw [report_exact]; rfl
  change (GeneralNominalAllocation.capture _ _ _ _ packet.bindings).inputs name = _
  rw [b]
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl <;> rfl

theorem binder_names (name : Nat) (member : name ∈ [0,1]) : plan.binder name = 1 := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl <;>
    simp only [Plan.binder,show declaration.outputNames = [] from rfl,List.not_mem_nil,ite_false] <;>
    rw [capture_names _ (by simp)] <;> rfl

theorem head_schema : plan.headSchema = { variables := [⟨0,.source 1,.actual⟩,⟨1,.source 1,.actual⟩] } := by
  unfold Plan.headSchema
  rw [query]
  simp [GeneralNominalMaterialization.schemas,GeneralNominalMaterialization.schema,
    GeneralNominalMaterialization.Schema.append,plan,rootSite,List.ofFn_succ]

theorem output_schema : outputSchema start.core root plan = { variables := [⟨0,.source 1,.actual⟩] } := by
  simp [outputSchema,requests_exact,Plan.schema,GeneralNominalMaterialization.generated,
    GeneralNominalInspection.translate,normalize,GeneralNominalMaterialization.schema,
    GeneralNominalMaterialization.Schema.append]

theorem effects_ready : EffectsReady start.core root plan := by
  constructor
  · intro output member
    rw [requests_exact] at member
    cases List.mem_singleton.mp member
    exact ⟨⟨0,0,.var 0⟩,by simp,rfl⟩
  · rw [output_schema]

theorem self_schema (assignment : GeneralNominalCommonBridge.Assignment) :
    plan.SchemaHolds { variables := [⟨0,.source 1,.actual⟩] } assignment := by
  constructor
  · intro test member; cases member
  · intro entry member
    cases List.mem_singleton.mp member
    simp only [ite_true,binder_names 0 (by simp)]
    exact ⟨⟨_,.source _⟩,⟨_,.source _⟩,by intro a b one two; cases one; cases two; exact ⟨subtype_refl _,subtype_refl _⟩⟩

theorem universal_head (assignment : GeneralNominalCommonBridge.Assignment) : HeadEquations plan assignment := by
  refine ⟨point_root_holds _ root (fun _ => rfl) assignment,?_,?_⟩
  · intro name member
    have present : name ∈ [0,1] := member
    rw [binder_names name present,capture_names name present]
    exact ⟨subtype_refl _,subtype_refl _⟩
  · rw [head_schema]
    constructor
    · intro test member; cases member
    · intro entry member
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl <;>
        simp only [ite_true,binder_names 0 (by simp),binder_names 1 (by simp)] <;>
        exact ⟨⟨_,.source _⟩,⟨_,.source _⟩,by intro a b one two; cases one; cases two; exact ⟨subtype_refl _,subtype_refl _⟩⟩

theorem output_equations : OutputEquations start.core root plan model := by
  constructor
  · rw [output_schema]
    exact self_schema model
  · intro first one last two _
    rw [requests_exact] at one two
    cases List.mem_singleton.mp one
    cases List.mem_singleton.mp two
    exact ⟨subtype_refl _,subtype_refl _⟩

theorem common_effects : ∃ assignment, GeneralNominalCenteredHeadStepEffects.Models start assignment ∧
    ChosenClassEffects registry start.core root 3 assignment :=
  ⟨model,inhabited,⟨children,unique⟩,plan,frame,effects_ready,universal_head model,output_equations⟩

theorem no_output_conflict : ¬ GeneralNominalCenteredHeadStepBoundary.OutputConflict registry start root 3 :=
  fun conflict => conflict.2 common_effects

private def height (source : Nat) : Nat := if source = 0 then 1 else 0

private theorem model_height (source : Nat) : (model source).1 = GeneralNominalOutputGrowth.tower (height source) := by
  by_cases zero : source = 0 <;> simp [height,zero,GeneralNominalOutputGrowth.tower] <;> rfl

theorem feedback_acyclic (identity : Nat) : ¬ GeneralNominalFeedbackK2.Cycle start.core.erased.current identity :=
  GeneralNominalOutputGrowthModels.feedback_acyclic _ model inhabited.1.1 height model_height
    (by rintro _ _ ⟨_,_,⟨kind,_,_,_⟩,_,_⟩; exact Fin.elim0 kind) identity

theorem no_raw_recurs (slot : Fin snapshot.base.slots) : ¬ GeneralNominalCycleK2.RecursAt snapshot slot :=
  GeneralNominalInitialNamedLocal189.no_raw_recurs slot

theorem centered_acyclic (origin : Origin) : ¬ GeneralNominalCenteredSteps.Cyclic start.core origin :=
  GeneralNominalCenteredSteps.initial_acyclic context root feedback_acyclic origin

theorem decision : GeneralNominalCenteredSteps.DecisionGuard registry start.core root := by
  have ready (slot : Fin 3) : GeneralNominalSharedSupport.ReadyAt start.core.erased slot.val := by
    by_cases zero : slot = 0
    · subst slot
      let head := GeneralNominalSupport.Head.nominal (snapshot := snapshot) 0
        (GeneralNominalCenteredTerminalForkSource.descriptor (some false)) rfl
      exact ⟨_,_,head,GeneralNominalSharedSupport.source_head _ head⟩
    · let head := GeneralNominalSupport.Head.scalar (snapshot := snapshot) slot .int
        (by simp [GeneralNominalCenteredTerminalForkSource.view,zero])
      exact ⟨_,_,head,GeneralNominalSharedSupport.source_head _ head⟩
  exact GeneralNominalCenteredSupport.legacy_decision ⟨fun _ => ready 1,fun _ _ _ _ _ slot _ => ready slot⟩

theorem safe : B4TargetV6.SafeKnown (GeneralNominalCenteredHeadWFBoundary.boundary roles) registry start root := by
  refine ⟨known,?_,?_,?_⟩
  · rintro ((⟨_,_,_,slot,_,cycle⟩ | ⟨_,_,_,cycle,_⟩) | ⟨_,_,_,_,cycle⟩)
    · exact no_raw_recurs slot cycle
    · exact feedback_acyclic _ cycle
    · exact centered_acyclic _ cycle
  · rintro ((⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩ | ⟨_,_,_,_,_,_,_,_,visited,_,cycle,_⟩) |
        ⟨_,_,_,_,_,_,_,_,_,_,_,cycle⟩)
    · exact no_raw_recurs visited.1 cycle
    · exact feedback_acyclic _ cycle
    · exact centered_acyclic _ cycle
  · rintro (⟨_,d,visible,_,_,unprepared⟩ | ⟨_,legacy⟩ | unjustified | unclosed)
    · cases List.mem_singleton.mp visible
      exact unprepared prepared
    · rcases legacy with ⟨⟨_,_,_,_,_,⟨⟨kind,_,_⟩,_⟩⟩,_⟩ |
        ⟨⟨_,_,_,_,_,_,_,_,_,_,⟨⟨kind,_,_⟩,_⟩⟩,_⟩ <;> exact Fin.elim0 kind
    · exact unjustified decision
    · exact unclosed (GeneralNominalCenteredAdministrativeLocal.initial_ready context root)

theorem selected : GeneralNominalCenteredHeadWFBoundary.Local registry start root (.selected 3 children) :=
  .selected safe unique no_output_conflict

theorem packet_models (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models snapshot assignment) : packet.Holds assignment := by
  have named : plan.SchemaHolds (GeneralNominalPacketSupport.namedSchema plan.packet) assignment := by
    rw [GeneralNominalInitialNamedEvidence189.initial_schema initial_source plan frame rfl,output_schema]
    exact self_schema assignment
  exact (GeneralNominalLinearNamedPlan189.named_plan plan [(0,(1 : Fin 3)),(1,1)] (by decide +kernel) query rfl rfl rfl
    assignment valid (universal_head assignment) named).1

theorem candidate_packet (candidate : Plan roles)
    (framed : Frame registry start.core root key candidate) : candidate.packet = packet := by
  have reg := framed.registry_eq
  have ctx : candidate.packet.context = context := framed.context_eq
  have site : candidate.packet.site = GeneralNominalDemandMerging.pointSite root := List.mem_singleton.mp framed.raw_recorded
  have decl : candidate.packet.declaration = declaration := List.mem_singleton.mp framed.visible
  cases candidate with
  | mk p input eq =>
    cases p with
    | mk pr pc ps pd checked pb =>
      simp only at reg ctx site decl
      subst pr; subst pc; subst ps; subst pd
      have bounds : pb = [((1 : Fin 3),(1 : Fin 3)),((1 : Fin 3),(1 : Fin 3))] := Option.some.inj framed.located.symm
      subst pb
      rfl

theorem candidate_committed (candidate : Plan roles)
    (framed : Frame registry start.core root key candidate) :
    GeneralNominalFeedbackSteps.Committed start.core.erased.current candidate.packet := by
  rw [candidate_packet candidate framed]
  constructor
  · intro assignment valid
    exact packet_models assignment valid.1
  · intro child member
    have empty := GeneralNominalHeadLeafPlan189.children_empty plan rfl
    change child ∈ plan.packet.children at member
    rw [empty] at member
    cases member

theorem stable : (GeneralNominalCenteredHeadWFBoundary.boundary roles).Stable registry start root := by
  intro focus generated after action
  have onlyRoot : ∀ focus, GeneralNominalSaturationState.Generated start.core.erased.current root focus → focus = root := by
    intro focus generated
    induction generated with
    | root => rfl
    | child prior member ih => cases member
    | alias prior one two same ih => exact congrArg GeneralNominalDemandMerging.Site.occurrence (List.mem_singleton.mp two)
  have same := onlyRoot focus generated
  cases action with
  | administrative focus after action =>
    cases action with
    | enqueue linked absent => exact absent _ (List.mem_singleton_self _) same.symm
    | refresh context certificate source member unknown known =>
        exact unknown (GeneralNominalCenteredTerminalForkSource.all_known _ source member)
    | equate first last one two equal novel =>
        exact novel (GeneralDictionaryReachableEvidenceInitial.initial_equal_is_raw context root first last equal)
    | reobserve revision certificate improved =>
        exact GeneralNominalReobservationSteps.pointClosed_no_revision
          (GeneralNominalCenteredTerminalForkSource.point_closed false) revision improved
  | refresh focus context certificate source member unknown known =>
      exact unknown (GeneralNominalCenteredTerminalForkSource.all_known _ source member)
  | install candidate support enabled novel =>
      exact novel (candidate_committed candidate (same ▸ enabled.frame))
  | merge first last support one two inputs novel guard =>
    have a := List.mem_singleton.mp one
    have b := List.mem_singleton.mp two
    subst first; subst last
    exact novel (.refl _)

theorem evidence : (GeneralNominalCenteredHeadWFBoundary.boundary roles).Evidence
    registry start model root (.node 3 []) := by
  apply (GeneralNominalSourceLinearEvidence190.stable_selected_evidence checked initial_source stable selected ?_).2 model inhabited
  intro d member _
  cases List.mem_singleton.mp member
  refine ⟨⟨[0,1],by decide +kernel,rfl⟩,rfl,?_,?_⟩
  · intro output member
    cases List.mem_singleton.mp member
    exact ⟨⟨0,0,.var 0⟩,List.mem_singleton_self _,rfl⟩
  · intro equation member
    cases List.mem_singleton.mp member
    simp [GeneralNominalInspection.translate,GeneralDeclarationPatterns.normalize,
      GeneralNominalHeadMatchMass.Complete]

theorem inhabited_stable_selected :
    Checked registry ∧ (GeneralNominalCenteredHeadWFBoundary.boundary roles).Initial registry root start ∧
      (GeneralNominalCenteredHeadWFBoundary.boundary roles).Stable registry start root ∧
      GeneralNominalCenteredHeadWFBoundary.Local registry start root (.selected 3 []) ∧
      GeneralNominalCenteredHeadStepEffects.Models start model ∧ (roles root.demand.role).arity = 2 ∧ root.demand.outputs ≠ [] ∧
      (GeneralNominalCenteredHeadWFBoundary.boundary roles).Evidence registry start model root (.node 3 []) := by
  refine ⟨checked,initial_source,stable,?_,inhabited,rfl,by decide +kernel,evidence⟩
  simpa only [GeneralNominalHeadLeafPlan189.children_empty plan rfl] using selected

end Yulang.GeneralNominalTwoHeadNonvacuity190
