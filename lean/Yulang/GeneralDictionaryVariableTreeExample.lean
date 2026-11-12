import Yulang.GeneralDictionaryVariableTree
import Yulang.GeneralNominalBranchExample

namespace Yulang.GeneralDictionaryVariableTreeExample
open GeneralDeclarations GeneralDeclarationPatterns GeneralNominalRecursiveCandidates
open GeneralNominalRecursiveInspection GeneralDictionaryRecursiveEvidence
open GeneralDeclarationExamples (roles constructors)
open GeneralNominalBranchExample (state context root model state_models parent)

abbrev clause : Clause := ⟨10,0,[.var 0],[]⟩
abbrev declaration : Declaration := ⟨41,0,[.app 5 [.var 0,.var 1]],[clause],[],[]⟩
abbrev leafDeclaration : Declaration := ⟨42,0,[.app 2 []],[],[],[]⟩
abbrev registry : Registry := ⟨constructors,roles,[declaration,leafDeclaration]⟩

theorem checked : DeclarationChecked constructors roles declaration := by
  constructor
  · simp [Declaration.Signature,Clause.Signature,roles,GeneralDeclarationExamples.bareRole]
  · simp [Declaration.Identified,Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly,Declaration.outputNames]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,normalizeArgs,normalize,variablesArgs,Pattern.variables]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,constructors]
  · intro c member
    have same := List.mem_singleton.mp member
    subst c
    exact ⟨rfl,rfl⟩
  · intro c member
    have same := List.mem_singleton.mp member
    subst c
    exact (checkSmaller_exact _ _).mp (by decide +kernel)
  · intro c member
    have same := List.mem_singleton.mp member
    subst c
    unfold ConservativeSmaller
    decide +kernel
  · intro c member
    have same := List.mem_singleton.mp member
    subst c
    intro capture
    constructor
    · simp [counted,substArgs,Pattern.subst,normalizeArgs,normalize,encodeArgs,Pattern.encode,Roles.argsSize,Roles.Term.size]
      omega
    · intro name
      simp [counted,substArgs,Pattern.subst,normalizeArgs,normalize,encodeArgs,Pattern.encode,Roles.argsOccurrences,Roles.Term.occurrences]

abbrev names : Fin 2 → Nat := Fin.val
abbrev bounds : Fin 2 → GeneralNominalInspection.Bounds state := fun i => if i = 0 then (1,1) else (2,2)
abbrev tree : GeneralNominalTreeFacts.Tree state names bounds 0 :=
  .leaf names bounds 0 parent rfl (by simp [List.ofFn_succ,bounds])

abbrev shape : GeneralDictionaryVariableTree.TreeBranchShape context root declaration where
  variables := by
    intro c member
    have same := List.mem_singleton.mp member
    subst c
    constructor
    · rfl
    · intro pattern member
      have same := List.mem_singleton.mp member
      subst pattern
      exact ⟨0,rfl⟩
  outputs := rfl
  role := rfl
  slot := 0
  arity := 2
  names := names
  distinct := fun _ _ equal => Fin.ext equal
  inputs := rfl
  bounds := bounds
  tree := tree
  query := by
    simp [GeneralNominalInspection.queries,Declaration.normalHead,normalizeArgs,normalize,GeneralNominalInspection.translate,GeneralNominalBranchExample.interpretation,GeneralNominalTreeFacts.Tree.query,List.ofFn_succ,names]
  located := rfl

theorem metadata : Metadata registry context := by
  refine ⟨rfl,?_⟩
  intro name base found
  cases found

abbrev children := GeneralNominalAllocation.children state registry root declaration checked
  (bindings state (report context declaration [(0,0)]))

theorem nonterminal : declaration.requirements ≠ [] := by intro h; cases h

theorem actual_children_count : children.length = 1 := by
  simp [children,GeneralNominalAllocation.children,GeneralDictionaryEmissionPlans.children,
    GeneralCanonicalChildOrder.canonicalEmit,GeneralDeclarationDemands.emitAll,
    GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements]

theorem actual_instance : Instance registry context model root declaration.id children :=
  GeneralDictionaryVariableTree.instance_of_shape context registry root declaration
    (by simp) checked shape metadata model state_models

theorem inhabited_nonterminal : GeneralNominalState.Models state model ∧
    Instance registry context model root declaration.id children ∧ children ≠ [] := by
  refine ⟨state_models,actual_instance,?_⟩
  intro empty
  have wrong := actual_children_count
  rw [empty] at wrong
  cases wrong

abbrev start := GeneralNominalSupport.initial context root

theorem initial_source : GeneralNominalSourceFormation.InitialSource registry context root where
  roles_agree := rfl
  metadata := metadata
  linked := by
    constructor
    · intro index; constructor <;> simp [GeneralNominalState.sources,List.ofFn_succ]
    · intro output member; cases member
  intervals := fun _ _ _ => CommonNominalFullCarrier.subtype_refl _
  below_seed := by
    intro source member
    simp [GeneralNominalState.sources,List.ofFn_succ] at member
    rcases member with h | h | h | h | h | h <;> subst source <;> decide +kernel
  unallocated := rfl

theorem initial_models : GeneralNominalSaturationState.Models start.current model :=
  (GeneralNominalSaturationState.initial_models context root model).mpr state_models

theorem actual_reachable :
    B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry root start :=
  ⟨start,⟨context,initial_source,rfl⟩,.refl⟩
end Yulang.GeneralDictionaryVariableTreeExample
