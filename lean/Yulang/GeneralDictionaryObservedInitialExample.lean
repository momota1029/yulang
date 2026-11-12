import Yulang.GeneralDictionaryObservedTreeBranch
import Yulang.GeneralDictionaryJointMergeExample
import Yulang.GeneralNominalSupportBoundary

/-! A genuine nonempty named-output request, not an empty-schema regression.
The output target is already justified as int by ordinary source observations. -/
namespace Yulang.GeneralDictionaryObservedInitialExample
open GeneralDeclarations GeneralDeclarationPatterns GeneralNominalRecursiveCandidates
open GeneralNominalRecursiveInspection GeneralDictionaryRecursiveEvidence
open GeneralDeclarationExamples (roles constructors displayChild)
open GeneralNominalExamples (model listDescriptor interpretation)

abbrev source : GeneralNominalState.State := {GeneralNominalExamples.state true with seed := 1}
abbrev context : GeneralNominalCandidates.Context := ⟨source,interpretation⟩
theorem source_models : GeneralNominalState.Models source model := GeneralNominalExamples.state_models true

abbrev equation : Equation := ⟨0,0,.app 2 []⟩
abbrev declaration : Declaration := ⟨45,1,[.app 0 [.var 0]],[displayChild],[equation],[]⟩
abbrev registry : Registry := ⟨constructors,roles,[declaration]⟩
abbrev demand : GeneralSourceState.Demand roles := ⟨1,fun _ => (0,0),[⟨0,1⟩],by
  intro o member
  have same := List.mem_singleton.mp member
  subst o
  exact ⟨none,rfl⟩⟩
abbrev root : GeneralSourceDictionaries.Occurrence roles := ⟨105,demand⟩

theorem checked : DeclarationChecked constructors roles declaration := by
  constructor
  · refine ⟨rfl,?_,?_,?_⟩
    · intro e member
      have same := List.mem_singleton.mp member; subst e
      exact ⟨none,rfl⟩
    · intro name body present
      by_cases zero : name = 0
      · subst name; exact Or.inl ⟨equation,by simp,rfl⟩
      · simp [roles,GeneralDeclarationExamples.outputRole,zero] at present
    · intro c member
      have same := List.mem_singleton.mp member; subst c
      exact ⟨rfl,by simp⟩
  · simp [Declaration.Identified,Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly,Declaration.outputNames]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,normalizeArgs,normalize,variablesArgs,Pattern.variables]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,constructors]
  · intro c member
    have same := List.mem_singleton.mp member; subst c
    exact ⟨rfl,rfl⟩
  · intro c member
    have same := List.mem_singleton.mp member; subst c
    exact (checkSmaller_exact _ _).mp (by decide +kernel)
  · intro c member
    have same := List.mem_singleton.mp member; subst c
    unfold ConservativeSmaller; decide +kernel
  · intro c member
    have same := List.mem_singleton.mp member; subst c
    exact unary_descent 0 0

abbrev tree : GeneralNominalTreeFacts.Tree source (n := 1) (fun _ => 0) (fun _ => (1,1)) 0 :=
  .leaf (fun _ => 0) (fun _ => (1,1)) 0 listDescriptor rfl (by simp [List.ofFn_succ])

theorem requests_exact : GeneralNominalMaterialization.requests source registry root declaration checked
    (bindings source (report context declaration [(0,0)])) =
    [⟨.app 2 [],1,.actual⟩] := by
  rw [GeneralDictionaryObservedScalarRequests.requests_root _ _ _ _ _ _ (by
    intro clause member
    have same := List.mem_singleton.mp member; subst clause
    exact ⟨rfl,by intro pattern member; have same := List.mem_singleton.mp member; subst pattern; exact ⟨0,rfl⟩⟩)]
  rfl

abbrev shape : GeneralDictionaryObservedTreeBranch.Shape context registry root declaration checked where
  role := rfl
  slot := 0
  arity := 1
  names := fun _ => 0
  distinct := fun _ _ _ => Subsingleton.elim _ _
  inputs := rfl
  bounds := fun _ => (1,1)
  tree := tree
  query := by
    simp [GeneralNominalInspection.queries,Declaration.normalHead,normalizeArgs,normalize,
      GeneralNominalInspection.translate,interpretation,GeneralNominalTreeFacts.Tree.query,List.ofFn_succ]
  located := rfl
  defined := by
    intro o member
    have same := List.mem_singleton.mp member; subst o
    exact ⟨equation,List.mem_singleton_self _,rfl⟩
  observed := by
    rw [requests_exact]
    intro request member
    have same := List.mem_singleton.mp member; subst request
    refine ⟨1,.int,rfl,rfl,?_⟩
    simp [normalize,normalizeArgs,GeneralNominalInspection.translate,interpretation]

theorem metadata : Metadata registry context := by
  refine ⟨rfl,?_⟩
  intro name base found
  change (if name = 2 then some (GeneralCandidateInspection.Primitive.scalar .int) else none) = some base at found
  split at found
  · subst name; cases found; exact ⟨_,rfl,rfl⟩
  · cases found

theorem named_request_present : root.demand.outputs ≠ [] := by intro h; cases h

theorem nonterminal : declaration.requirements ≠ [] := by intro h; cases h

theorem every_source_model (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models source assignment) :
    BranchModels registry context root declaration checked [(0,0)] assignment :=
  GeneralDictionaryObservedTreeBranch.branch_models context registry root declaration checked shape assignment valid

theorem actual_instance : Instance registry context model root declaration.id
    (GeneralNominalAllocation.children source registry root declaration checked
      (bindings source (report context declaration [(0,0)]))) :=
  GeneralDictionaryObservedTreeBranch.instance_of_shape context registry root declaration
    (List.mem_singleton_self _) checked shape metadata model source_models
abbrev start := GeneralNominalSupport.initial context root
abbrev children := GeneralNominalAllocation.children source registry root declaration checked
  (bindings source (report context declaration [(0,0)]))

theorem initial_source : GeneralNominalSourceFormation.InitialSource registry context root where
  roles_agree := rfl
  metadata := metadata
  linked := by
    constructor
    · intro index; constructor <;> simp [GeneralNominalState.sources,List.ofFn_succ]
    · intro output member
      have same := List.mem_singleton.mp member
      subst output
      simp [GeneralNominalState.sources,List.ofFn_succ]
  intervals := fun _ _ _ => CommonNominalFullCarrier.subtype_refl _
  below_seed := by
    intro id member
    simp [GeneralNominalState.sources,List.ofFn_succ] at member
    rcases member with h | h | h | h <;> subst id <;> decide +kernel
  unallocated := rfl

theorem initial_models : GeneralNominalSaturationState.Models start.current model :=
  (GeneralNominalSaturationState.initial_models context root model).mpr source_models

theorem actual_reachable :
    B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry root start :=
  ⟨start,⟨context,initial_source,rfl⟩,.refl⟩

theorem root_ready : ¬ GeneralNominalState.RootPending source root.demand := by
  rintro ⟨index,unknown⟩
  exact unknown ⟨0,rfl,Or.inr ⟨listDescriptor,rfl⟩⟩

theorem prepared : Prepared registry context root declaration checked := by
  refine ⟨metadata,initial_source.linked,
    GeneralNominalSourceFormation.initial_fresh context initial_source root.identity,
    [(0,0)],rfl,?_,GeneralDictionaryObservedTreeBranch.ready context registry root declaration checked shape,
    model,every_source_model model source_models⟩
  rw [GeneralNominalTreeFacts.report_exact context declaration tree shape.query]
  exact GeneralNominalTreeFacts.tree_finished source tree none

theorem survivor : Survivor registry context root declaration.id children :=
  ⟨root_ready,declaration,by simp,checked,rfl,rfl,[(0,0)],rfl,prepared,rfl⟩

theorem initial_joint : GeneralNominalJointCandidates.Joint registry start.current root declaration.id :=
  GeneralNominalJointCandidates.initial_joint registry context root declaration (by simp) checked rfl
    [(0,0)] rfl prepared model (every_source_model model source_models)

theorem actual_children_count : children.length = 1 := by
  simp [children,GeneralNominalAllocation.children,GeneralDictionaryEmissionPlans.children,
    GeneralCanonicalChildOrder.canonicalEmit,GeneralDeclarationDemands.emitAll,
    GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements]

end Yulang.GeneralDictionaryObservedInitialExample
