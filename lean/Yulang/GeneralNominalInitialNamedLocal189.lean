import Yulang.GeneralNominalInitialNamedFixture189
import Yulang.GeneralNominalSingleVariableModels189

set_option backward.isDefEq.respectTransparency false

/-! Nonvacuous actual head selection for the reused scalar leaf fixture. -/
namespace Yulang.GeneralNominalInitialNamedLocal189
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralNominalCenters GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralNominalCenteredHeadOutputs CommonNominalFullCarrier
open GeneralNominalInitialNamedFixture189

theorem known : ¬ GeneralNominalState.RootPending snapshot root.demand := by
  rintro ⟨index,unknown⟩
  exact unknown ⟨(1 : Fin 3),rfl,Or.inl (by decide +kernel)⟩

theorem survivor : GeneralNominalCenteredHeadCandidates.Survivor registry context root 3 children :=
  ⟨known,declaration,List.mem_singleton_self _,declaration_checked,rfl,rfl,[(1,1)],rfl,prepared,rfl⟩

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

theorem binder_zero : plan.binder 0 = 1 := by
  unfold Plan.binder GeneralNominalPacketSupport.capture
  have b : packet.bindings = [(0,1,1)] := by
    change bindings snapshot (report context declaration [(1,1)]) = _
    rw [report_exact]
    rfl
  change (if 0 ∈ declaration.outputNames then _ else _) = _
  simp only [show ¬ 0 ∈ declaration.outputNames from by decide +kernel,ite_false]
  rw [b]
  rfl

theorem head_schema : plan.headSchema = { variables := [⟨0,.source 1,.actual⟩] } := by
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
    simp only [ite_true,binder_zero]
    exact ⟨⟨_,.source _⟩,⟨_,.source _⟩,by intro a b one two; cases one; cases two; exact ⟨subtype_refl _,subtype_refl _⟩⟩

theorem head_equations : HeadEquations plan model := by
  refine ⟨point_root_holds _ root (fun _ => rfl) model,?_,?_⟩
  · intro name member
    have equal : name = 0 := List.mem_singleton.mp member
    subst name
    rw [binder_zero]
    have cap : (GeneralNominalPacketSupport.capture plan.packet).inputs 0 = (1,1) := by
      unfold GeneralNominalPacketSupport.capture
      have b : packet.bindings = [(0,1,1)] := by
        change bindings snapshot (report context declaration [(1,1)]) = _
        rw [report_exact]; rfl
      change (GeneralNominalAllocation.capture _ _ _ _ packet.bindings).inputs 0 = _
      rw [b]
      rfl
    rw [cap]
    exact ⟨subtype_refl _,subtype_refl _⟩
  · rw [head_schema]
    exact self_schema model

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
  ⟨model,inhabited,⟨children,unique⟩,plan,frame,effects_ready,head_equations,output_equations⟩

theorem no_output_conflict : ¬ GeneralNominalCenteredHeadStepBoundary.OutputConflict registry start root 3 :=
  fun conflict => conflict.2 common_effects

private def height (source : Nat) : Nat := if source = 0 then 1 else 0

private theorem model_height (source : Nat) : (model source).1 = GeneralNominalOutputGrowth.tower (height source) := by
  by_cases zero : source = 0 <;> simp [height,zero,GeneralNominalOutputGrowth.tower] <;> rfl

theorem feedback_acyclic (identity : Nat) : ¬ GeneralNominalFeedbackK2.Cycle start.core.erased.current identity :=
  GeneralNominalOutputGrowthModels.feedback_acyclic _ model inhabited.1.1 height model_height
    (by rintro _ _ ⟨_,_,⟨kind,_,_,_⟩,_,_⟩; exact Fin.elim0 kind) identity

theorem raw_acyclic (slot : Fin snapshot.base.slots) : ¬ GeneralNominalCycleK2.Cycle snapshot slot := by
  have decreasing : ∀ first last, GeneralNominalMixedRecurrence.Edge snapshot first last →
      height last.val < height first.val := by
    intro first last edge
    rcases edge with ⟨kind,_,_,_⟩ | argument
    · exact Fin.elim0 kind
    · obtain ⟨descriptor,recorded,index,actual,seen,same⟩ :=
        GeneralNominalMixedRecurrence.actual_edge_sound _ _ _ argument model source_model
      exact GeneralNominalOutputGrowthModels.observation_decreases model height model_height _ _ _ _ actual seen same
  have paths : ∀ first last, GeneralNominalMixedRecurrence.Path snapshot first last → height last.val ≤ height first.val := by
    intro first last path
    induction path with
    | nil => exact Nat.le_refl _
    | cons edge _ ih => exact Nat.le_trans ih (Nat.le_of_lt (decreasing _ _ edge))
  rintro ⟨next,edge,path⟩
  have smaller := decreasing _ _ edge
  have larger := paths _ _ path
  omega

theorem no_raw_recurs (slot : Fin snapshot.base.slots) : ¬ GeneralNominalCycleK2.RecursAt snapshot slot := by
  rintro (⟨child,edge,path⟩ | ⟨cycle,_⟩)
  · exact raw_acyclic slot ⟨child,GeneralNominalCycleK2.direct_edge_sound edge,GeneralNominalCycleK2.direct_path_sound path⟩
  · exact raw_acyclic slot cycle

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

theorem value_support : GeneralNominalValueSupport.PacketGuard start.core.erased packet [] :=
  GeneralNominalCenteredHeadStepAvailability.selected_initial_value
    (GeneralNominalCenteredHeadWFBoundary.local_iff.mp selected) frame

end Yulang.GeneralNominalInitialNamedLocal189
