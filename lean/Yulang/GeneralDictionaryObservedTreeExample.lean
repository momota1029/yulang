import Yulang.GeneralDictionaryObservedTreeBranch
import Yulang.GeneralDictionaryJointMergeExample

/-! A genuine nonempty named-output request, not an empty-schema regression.
The output target is already justified as int by ordinary source observations. -/
namespace Yulang.GeneralDictionaryObservedTreeExample
open GeneralDeclarations GeneralDeclarationPatterns GeneralNominalRecursiveCandidates
open GeneralNominalRecursiveInspection GeneralDictionaryRecursiveEvidence
open GeneralDeclarationExamples (roles constructors displayChild)
open GeneralNominalExamples (state context model state_models listDescriptor interpretation)

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

abbrev tree : GeneralNominalTreeFacts.Tree (state true) (n := 1) (fun _ => 0) (fun _ => (1,1)) 0 :=
  .leaf (fun _ => 0) (fun _ => (1,1)) 0 listDescriptor rfl (by simp [List.ofFn_succ])

theorem requests_exact : GeneralNominalMaterialization.requests (state true) registry root declaration checked
    (bindings (state true) (report (context true) declaration [(0,0)])) =
    [⟨.app 2 [],1,.actual⟩] := by
  rw [GeneralDictionaryObservedScalarRequests.requests_root _ _ _ _ _ _ (by
    intro clause member
    have same := List.mem_singleton.mp member; subst clause
    exact ⟨rfl,by intro pattern member; have same := List.mem_singleton.mp member; subst pattern; exact ⟨0,rfl⟩⟩)]
  rfl

abbrev shape : GeneralDictionaryObservedTreeBranch.Shape (context true) registry root declaration checked where
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

theorem metadata : Metadata registry (context true) := by
  refine ⟨rfl,?_⟩
  intro name base found
  change (if name = 2 then some (GeneralCandidateInspection.Primitive.scalar .int) else none) = some base at found
  split at found
  · subst name; cases found; exact ⟨_,rfl,rfl⟩
  · cases found

theorem named_request_present : root.demand.outputs ≠ [] := by intro h; cases h

theorem nonterminal : declaration.requirements ≠ [] := by intro h; cases h

theorem every_source_model (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models (state true) assignment) :
    BranchModels registry (context true) root declaration checked [(0,0)] assignment :=
  GeneralDictionaryObservedTreeBranch.branch_models (context true) registry root declaration checked shape assignment valid

theorem actual_instance : Instance registry (context true) model root declaration.id
    (GeneralNominalAllocation.children (state true) registry root declaration checked
      (bindings (state true) (report (context true) declaration [(0,0)]))) :=
  GeneralDictionaryObservedTreeBranch.instance_of_shape (context true) registry root declaration
    (List.mem_singleton_self _) checked shape metadata model (state_models true)
end Yulang.GeneralDictionaryObservedTreeExample
