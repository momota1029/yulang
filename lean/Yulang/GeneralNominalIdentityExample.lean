import Yulang.GeneralNominalIdentityBudget
import Yulang.GeneralNominalOutputGrowthModels
import Yulang.CommonRigidHeadInspection

/-! A checked identity leaf installs a new equation at a distinct output ID.
The original output is unconstrained, and the source input is int. -/
namespace Yulang.GeneralNominalIdentityExample
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralNominalSaturationState GeneralNominalRecursiveCandidates
open GeneralNominalIdentityLeaf GeneralNominalIdentityProvenance
open GeneralNominalRecursiveInspection CommonNominalFullCarrier

abbrev roles : Roles.RoleDecls := fun _ => GeneralDeclarationExamples.outputRole 0
abbrev constructors : Constructors := fun _ => none
abbrev declaration : Declaration := ⟨0,0,[.var 0],[],[⟨0,0,.var 0⟩],[]⟩

theorem declaration_checked : DeclarationChecked constructors roles declaration := by
  constructor
  · refine ⟨rfl,?_,?_,by simp⟩
    · intro equation member; cases List.mem_singleton.mp member; exact ⟨none,rfl⟩
    · intro name body found
      by_cases zero : name = 0
      · subst name; exact Or.inl ⟨⟨0,0,.var 0⟩,by simp,rfl⟩
      · simp [zero] at found
  · simp [Declaration.Identified,Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly,Declaration.outputNames]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,
      normalizeArgs,normalize,variablesArgs,Pattern.variables]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped]
  all_goals intro clause member; cases member

abbrev registry : Registry := ⟨constructors,roles,[declaration]⟩
theorem checked : Checked registry := ⟨by simp,by intro d member; cases List.mem_singleton.mp member; exact declaration_checked⟩
theorem shape : Shape declaration := ⟨rfl,rfl,by intro e member; cases List.mem_singleton.mp member; rfl⟩
theorem registry_shape : RegistryShape registry := by intro d member; cases List.mem_singleton.mp member; exact shape

abbrev base : GeneralSourceState.State where
  slots := 2
  source := Fin.val
  source_injective := fun _ _ equal => Fin.ext equal
  rowSource := Fin.val
  ordinary := GeneralSourceState.equationAtoms 0 (.base .int)
  kinds := 0
  shapes := Fin.elim0
  shapes_injective := by intro i; exact Fin.elim0 i
  heads := fun slot => if slot = 0 then .scalar .int else .unresolved
  intervals := []
  heads_sound := by
    intro assignment valid slot term recorded
    by_cases same : slot = 0
    · subst slot
      have equal : term = .base .int := by simpa [GeneralSourceState.Head.equation] using recorded.symm
      subst term
      exact (GeneralSourceState.equationAtoms_exact _ _ assignment).mp valid
    · simp [same,GeneralSourceState.Head.equation] at recorded
  intervals_sound := by intro _ _ _ impossible; cases impossible

abbrev view : GeneralNormalizedObservation.Snapshot base where
  kinds := 0
  shapes := Fin.elim0
  shapes_injective := by intro i; exact Fin.elim0 i
  canonical := by intro i; exact Fin.elim0 i
  heads := fun slot => if slot = 0 then .scalar .int else .deferred .unresolved
  checked := by
    intro slot term recorded
    split at recorded
    · rename_i same; subst slot
      cases Option.some.inj recorded
      exact .head rfl
    · cases recorded

abbrev snapshot := GeneralNominalState.embed base view constructors
abbrev interpretation : GeneralNominalInspection.Interpretation :=
  ⟨fun _ => none,fun _ => false,by intro _ impossible; cases impossible⟩
abbrev context : Context := ⟨snapshot,interpretation⟩
abbrev root : Occurrence roles := ⟨0,⟨0,fun _ => (0,0),[⟨0,1⟩],by
  intro output member; cases List.mem_singleton.mp member; exact ⟨none,rfl⟩⟩⟩
abbrev start := GeneralNominalSupport.initial context root
abbrev packet : Packet roles :=
  ⟨registry,context,GeneralNominalDemandMerging.pointSite root,declaration,declaration_checked,[(0,0)]⟩

theorem point : Point root 0 := by simp [Point,List.ofFn_succ]
theorem source_member (slot : Fin 2) : slot.val ∈ GeneralNominalState.sources snapshot :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨slot,rfl⟩)))
theorem source : GeneralNominalSourceFormation.InitialSource registry context root := by
  refine ⟨rfl,⟨rfl,by intro _ _ impossible; cases impossible⟩,?_,?_,?_,rfl⟩
  · refine ⟨fun _ => ⟨source_member 0,source_member 0⟩,?_⟩
    intro output member; cases List.mem_singleton.mp member; exact source_member 1
  · intro model valid index; exact subtype_refl _
  · intro identity member
    simp [GeneralNominalState.sources,snapshot,GeneralNominalState.embed,base,
      GeneralSourceState.equationAtoms,List.ofFn_succ] at member
    rcases member with same | same | same | same <;> subst identity <;> decide +kernel

def commonModel (output : Inference.Base) : GeneralSourceState.Assignment :=
  fun name => (.base (if name = 0 then .int else output),Common.rowEmpty)
def model (output : Inference.Base) := GeneralNominalCommonBridge.lift (commonModel output)

theorem source_models (output : Inference.Base) : GeneralNominalState.Models snapshot (model output) := by
  apply (GeneralNominalState.embed_models ..).mpr
  apply (GeneralSourceState.models_ordinary _ _).mpr
  apply (GeneralSourceState.equationAtoms_exact _ _ _).mpr
  exact Common.equivalent_refl _

theorem branch : packet.Holds (model .int) := by
  apply (GeneralNominalPacketSupport.packet_exact packet _).mpr
  refine ⟨source_models .int,inputs_valid shape rfl _,(outputs_exact shape rfl _).mpr ?_⟩
  intro target member
  have same : target = 1 := by simpa [targets,GeneralNominalMaterialization.rootRequests,packet,GeneralNominalDemandMerging.pointSite,root] using member
  subst target
  exact ⟨subtype_refl _,subtype_refl _⟩

theorem novel : ¬ GeneralNominalFeedbackSteps.Committed start.current packet := by
  intro committed
  have valid := committed.1 (model .str) ((initial_models ..).mpr (source_models .str))
  have equal := (outputs_exact shape rfl (model .str)).mp
    ((GeneralNominalPacketSupport.packet_exact packet _).mp valid).2.2 1 (by simp [targets,GeneralNominalMaterialization.rootRequests,GeneralNominalDemandMerging.pointSite,root])
  have old : Common.Subtype (.base .str) (.base .int) := (CommonNominalFullModelMap.subtype_exact _ _).mp equal.1
  cases (CommonRigidHeadInspection.base_iff .str .int).mp old

theorem located : arguments context root = some packet.bounds := by decide +kernel

theorem prepared : Prepared registry context root declaration declaration_checked := by
  refine ⟨source.metadata,source.linked,GeneralNominalSourceFormation.initial_fresh context source root.identity,
    packet.bounds,located,?_,?_,model .int,branch⟩
  · rw [show packet.bounds = [(0,0)] from rfl,report_exact shape]
    exact ⟨rfl,rfl,rfl⟩
  · constructor
    · intro output member; cases List.mem_singleton.mp member
      exact ⟨⟨0,0,.var 0⟩,by simp,rfl⟩
    · change (GeneralNominalPacketSupport.namedSchema packet).unknown = false
      rw [named_schema shape]; rfl

theorem ready : ¬ GeneralNominalState.RootPending snapshot root.demand := by
  rintro ⟨index,unknown⟩
  apply unknown
  exact ⟨0,rfl,Or.inl (by simp [GeneralNormalizedObservation.Snapshot.graph,GeneralNormalizedObservation.Head.node])⟩

theorem no_raw (slot : Fin 2) : ¬ GeneralNominalCycleK2.RecursAt snapshot slot := by
  intro recurrence
  obtain ⟨child,edge,path⟩ := GeneralNominalCycleK2.recurs_cycle _ _ recurrence
  rcases edge with ⟨kind,_,_⟩ | ⟨descriptor,recorded,_⟩
  · exact Fin.elim0 kind
  · cases recorded

theorem no_feedback (identity : Nat) : ¬ GeneralNominalFeedbackK2.Cycle start.current identity :=
  GeneralNominalOutputGrowthModels.feedback_acyclic _ (model .int) ((initial_models ..).mpr (source_models .int))
    (fun _ => 0) (by intro name; simp [model,commonModel,GeneralNominalCommonBridge.lift,GeneralNominalOutputGrowth.tower]; rfl)
    (by rintro _ _ ⟨_,_,⟨kind,_,_⟩,_,_⟩; exact Fin.elim0 kind) identity

theorem no_root : ¬ GeneralNominalFeedbackK2.RootK2 start.current root := by
  rintro (⟨_,_,_,slot,_,cycle⟩ | ⟨_,_,index,cycle,_⟩)
  · exact no_raw slot cycle
  · exact no_feedback _ cycle

theorem no_candidate : ¬ GeneralNominalFeedbackK2.CandidateK2 registry start.current root := by
  rintro (⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩ | ⟨_,_,_,_,_,_,_,_,visited,_,cycle,_⟩)
  · exact no_raw visited.1 cycle
  · exact no_feedback _ cycle

theorem survivor : Survivor registry context root declaration.id packet.children :=
  ⟨ready,declaration,by simp,declaration_checked,rfl,rfl,packet.bounds,located,prepared,rfl⟩

theorem selected : GeneralNominalFeedbackK2.Local registry start.current root (.selected declaration.id packet.children) := by
  refine .selected ⟨ready,no_root,no_candidate,?_⟩ ⟨survivor,?_⟩
  · rintro (pending | ⟨_,legacy⟩)
    · obtain ⟨_,d,visible,certified,role,failed,missing⟩ := pending
      cases List.mem_singleton.mp visible
      exact missing prepared
    · rcases legacy with ⟨⟨_,_,_,slot,_,cycle⟩,_⟩ | ⟨⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩,_⟩
      all_goals obtain ⟨⟨kind,_,_⟩,_⟩ := cycle; exact Fin.elim0 kind
  · intro key children found
    have copy := found
    obtain ⟨_,d,visible,certified,identity,role,_⟩ := found
    cases List.mem_singleton.mp visible
    subst key
    exact ⟨rfl,survivor_children_functional registry checked context root declaration.id children packet.children copy survivor⟩

theorem enabled : GeneralNominalFeedbackSteps.Installable registry start.current packet := by
  refine ⟨⟨rfl,rfl,by simp [start,GeneralNominalSupport.initial,GeneralNominalSaturationState.initial],
    by simp,rfl,located,prepared,GeneralNominalFeedbackK2.selected_legacy selected,?_,?_,?_,?_⟩,selected,?_⟩
  · intro prior member; cases member
  · intro other member same; cases List.mem_singleton.mp member; exact .refl _
  · exact ⟨model .int,(initial_models ..).mpr (source_models .int),branch⟩
  · exact GeneralNominalJointCandidates.initial_joint registry context root declaration (by simp) declaration_checked rfl
      packet.bounds located prepared (model .int) branch
  · intro other member same; cases List.mem_singleton.mp member; exact .refl _

theorem decisions : GeneralNominalSupport.DecisionGuard start registry root [] := by
  refine ⟨(by intro _ impossible; cases impossible),?_,?_⟩
  · intro index
    exact GeneralNominalSupport.source_ready start 0 (.scalar .int) _ _
      (GeneralNominalSupport.Head.scalar (snapshot := snapshot) 0 .int rfl)
      (GeneralNominalSupport.Head.scalar (snapshot := snapshot) 0 .int rfl) []
  · intro d visible role bounds locatedHere slot member
    cases List.mem_singleton.mp visible
    have same := Option.some.inj (located.symm.trans locatedHere)
    subst bounds
    change slot ∈ GeneralNominalSupport.readsMany snapshot
      (GeneralNominalInspection.queries snapshot interpretation declaration) [(0,0)] at member
    rw [reads_empty shape context (0 : Fin 2)] at member
    cases member

theorem guard : GeneralNominalSharedSteps.PacketGuard start packet [] := by
  have old : GeneralNominalSupportChoices.PacketGuard start packet [] :=
    ⟨⟨decisions.1,decisions.2.1,decisions.2.2 declaration (by simp) rfl packet.bounds located⟩,decisions⟩
  exact GeneralNominalSharedSteps.leaf_guard rfl
    (GeneralNominalSharedPositive.leaf_input_coherent packet rfl)
    (GeneralNominalValueSupport.source_packet _ _ old)
    (GeneralNominalSharedPositive.initial_decision context root root registry [] decisions)

noncomputable def finish := GeneralNominalSharedSteps.install start packet []

theorem actual_step : GeneralNominalSharedSteps.Step registry root start finish :=
  ⟨root,.root,.install packet [] enabled novel guard⟩

theorem installed_alias : GeneralNominalIdentityBudget.AliasHeld finish 0 1 := by
  intro m valid
  have branch := (GeneralNominalSharedSteps.installed_committed start packet []).1 m valid
  exact (outputs_exact shape rfl m).mp ((GeneralNominalPacketSupport.packet_exact packet m).mp branch).2.2 1
    (by simp [targets,GeneralNominalMaterialization.rootRequests,GeneralNominalDemandMerging.pointSite,root])

theorem accessible : Acc (fun next current => GeneralNominalSharedSteps.Step registry root current next) start :=
  GeneralNominalIdentityBudget.checked_initial_accessible registry_shape checked point source

end Yulang.GeneralNominalIdentityExample
