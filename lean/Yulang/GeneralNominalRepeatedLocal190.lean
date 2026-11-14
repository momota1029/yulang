import Yulang.GeneralNominalRepeatedFixture190
import Yulang.GeneralNominalSourceRepeatedEvidence190
import Yulang.GeneralNominalCenteredHeadWFJoinCounterexample

set_option backward.isDefEq.respectTransparency false

/-! Nonvacuous actual head selection for the reused scalar leaf fixture. -/
namespace Yulang.GeneralNominalRepeatedLocal190
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralNominalCenters GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralNominalCenteredHeadOutputs CommonNominalFullCarrier
open GeneralNominalRepeatedFixture190

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

theorem binder_zero : plan.binder 0 = fresh snapshot.seed root.identity declaration.id 8 0 0 := by
  have different : fresh snapshot.seed root.identity declaration.id 0 0 0 ≠
      fresh snapshot.seed root.identity declaration.id 1 0 0 :=
    GeneralNominalCenteredAllocation.fresh_namespaces (by decide +kernel)
  simp only [Plan.binder,show declaration.outputNames = [] from rfl,List.not_mem_nil,ite_false]
  rw [capture_zero]
  simp only [different,ite_false]
  rfl

theorem head_schema : plan.headSchema = { variables := [⟨0,.source 1,.actual⟩,⟨0,.source 1,.actual⟩] } := by
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

theorem source_binder_same : GeneralNominalOriginTerms.Same model (.source 1) (.source (plan.binder 0)) := by
  refine ⟨⟨_,.source _⟩,⟨_,.source _⟩,?_⟩
  intro first last one two
  cases one; cases two
  rw [binder_zero,model_fresh]
  exact ⟨subtype_refl _,subtype_refl _⟩

theorem self_schema : plan.SchemaHolds { variables := [⟨0,.source 1,.actual⟩] } model := by
  constructor
  · intro test member; cases member
  · intro entry member
    cases List.mem_singleton.mp member
    exact source_binder_same

theorem head_equations : HeadEquations plan model := by
  refine ⟨point_root_holds _ root (fun _ => rfl) model,?_,?_⟩
  · intro name member
    have present : name = 0 := by
      simpa only [show declaration.inputNames = [0,0] from rfl,List.mem_cons,List.not_mem_nil,or_false,or_self] using member
    subst name
    rw [binder_zero,capture_zero]
    unfold GeneralNominalCaptureMerges.Fits
    rw [model_fresh,model_fresh,model_fresh]
    exact ⟨subtype_refl _,subtype_refl _⟩
  · rw [head_schema]
    constructor
    · intro test member; cases member
    · intro entry member
      simp only [List.mem_cons,List.not_mem_nil,or_false,or_self] at member
      subst entry
      exact source_binder_same

theorem output_equations : OutputEquations start.core root plan model := by
  constructor
  · rw [output_schema]
    exact self_schema
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

theorem installable : ∃ support, GeneralNominalCenteredHeadStepKernel.Installable registry start plan support := by
  apply GeneralNominalSourceRepeatedEvidence190.selected_installable checked initial_source selected plan frame [0,0] rfl rfl
  · intro output member
    cases List.mem_singleton.mp member
    exact ⟨⟨0,0,.var 0⟩,by simp,rfl⟩
  · intro equation member
    cases List.mem_singleton.mp member
    simp [normalize,GeneralNominalInspection.translate,GeneralNominalHeadMatchMass.Complete]

abbrev mergeLower := fresh snapshot.seed root.identity declaration.id 0 0 0

noncomputable def badModel : GeneralNominalCommonBridge.Assignment := fun identity =>
  if identity = mergeLower then (.base .bool,(model identity).2) else model identity

theorem lower_above : snapshot.seed < mergeLower :=
  GeneralNominalIdentities.source_above_seed snapshot.seed (root.identity,declaration.id,0,0,0)

theorem bad_preserves_source (identity : Nat) (member : identity ∈ GeneralNominalState.sources snapshot) :
    badModel identity = model identity := by
  have below : identity ≤ snapshot.seed := source.below_seed identity member
  have different : identity ≠ mergeLower := by have above := lower_above; omega
  simp only [badModel,different,ite_false]

theorem bad_source_model : GeneralNominalState.Models snapshot badModel :=
  GeneralNominalCenteredModelExtension.source_models_same snapshot
    (fun identity member => (bad_preserves_source identity member).symm) source_model

theorem bad_inhabited : GeneralNominalCenteredHeadStepEffects.Models start badModel :=
  (GeneralNominalHeadInitialCommon188.initial_models_iff context (fun _ => rfl) badModel).mpr bad_source_model

theorem bad_lower : (badModel mergeLower).1 = (.base .bool : Ty) := by
  simp only [badModel,ite_true]

theorem bad_one : (badModel 1).1 = (.base .int : Ty) := by
  rw [bad_preserves_source 1 (by simp [GeneralNominalState.sources,List.ofFn_succ])]
  rfl

theorem bool_not_below_int : ¬ Subtype (.base .bool) (.base .int) := by
  intro equal
  have impossible := equal 0
  change CommonNominalFullDemand.ProducerLe Common.rowLe (.base .bool) (.base .int) at impossible
  have different := (CommonNominalFullDemand.producerLe_iff_probe _ _).mp impossible 0
    ⟨fun _ => .bottom,fun _ => []⟩ (.base .int) rfl
  cases different

theorem bad_packet : ¬ packet.Holds badModel := by
  intro holds
  have ordinary := ((GeneralNominalPacketSupport.private_exact packet badModel).mp holds.1).2
  have member : (.tyLe (.var mergeLower) (.union (.var 1) (.var 1)) : PresenceNormalForm.Atom Nat) ∈
      GeneralNominalAllocation.merges snapshot registry root.identity declaration packet.bindings := by
    rw [bindings_exact]
    simp [GeneralNominalAllocation.merges,Declaration.inputNames,GeneralDeclarationPatterns.normalizeArgs,
      GeneralDeclarationPatterns.normalize,GeneralDeclarationPatterns.variablesArgs,GeneralDeclarationPatterns.Pattern.variables,
      GeneralNominalAllocation.occurrences,GeneralNominalAllocation.capture,GeneralNominalAllocation.equations,
      GeneralNominalAllocation.lower,GeneralNominalAllocation.upper,GeneralNominalAllocation.source,
      GeneralNominalAllocation.origin,mergeLower,fresh]
  have below := ordinary.2.1 _ member
  change Subtype (badModel mergeLower).1 (.union (badModel 1).1 (badModel 1).1) at below
  rw [bad_lower,bad_one] at below
  exact bool_not_below_int (subtype_trans below
    ((common_union_is_join ..).mpr ⟨subtype_refl _,subtype_refl _⟩))

theorem not_committed : ¬ GeneralNominalFeedbackSteps.Committed start.core.erased.current packet := by
  intro committed
  exact bad_packet (committed.1 badModel bad_inhabited.1.1)

theorem inhabited_step : ∃ after,
    (GeneralNominalCenteredHeadWFBoundary.boundary roles).Step registry root start after ∧
      ∃ assignment, GeneralNominalCenteredHeadStepEffects.Models after assignment := by
  obtain ⟨support,enabled⟩ := installable
  refine ⟨GeneralNominalCenteredHeadStepKernel.install start plan support enabled,?_,
    GeneralNominalCenteredHeadStepKernel.installed_inhabited enabled⟩
  exact ⟨root,GeneralNominalSaturationState.Generated.root,.install plan support enabled not_committed⟩

theorem not_stable : ¬ (GeneralNominalCenteredHeadWFBoundary.boundary roles).Stable registry start root := by
  obtain ⟨after,⟨focus,generated,action⟩,_⟩ := inhabited_step
  exact fun stable => stable focus generated after action

end Yulang.GeneralNominalRepeatedLocal190
