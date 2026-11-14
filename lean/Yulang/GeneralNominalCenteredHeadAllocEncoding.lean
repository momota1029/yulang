import Yulang.GeneralNominalCenteredHeadMatCompletionCollision

set_option backward.isDefEq.respectTransparency false

/-! Compile clause-local equation identities into injective allocation keys.
The source registry is retained by the boundary; only its internal allocation
view changes. Shared output binder names and all type patterns are unchanged. -/
namespace Yulang.GeneralNominalCenteredHeadAllocEncoding
open GeneralDeclarations GeneralRegistryReordering

def equation (clause : Nat) (value : Equation) : Equation :=
  { value with id := GeneralNominalIdentities.pair clause value.id }

def clause (value : Clause) : Clause :=
  { value with outputs := value.outputs.map (equation value.id) }

def binder (value : OutputBinder) : OutputBinder :=
  { value with equation := GeneralNominalIdentities.pair value.clause value.equation }

def declaration (value : Declaration) : Declaration :=
  { value with requirements := value.requirements.map clause
               outputBinders := value.outputBinders.map binder }

def registry (value : Registry) : Registry :=
  { value with declarations := value.declarations.map declaration }

@[simp] theorem inputNames (value : Declaration) : (declaration value).inputNames = value.inputNames := rfl

@[simp] theorem outputNames (value : Declaration) : (declaration value).outputNames = value.outputNames := by
  simp [Declaration.outputNames,declaration,binder,List.map_map,Function.comp_def]

theorem equation_key {first last a b : Nat} :
    GeneralNominalIdentities.pair first a = GeneralNominalIdentities.pair last b ↔ first = last ∧ a = b := by
  constructor
  · intro same
    have pair : (first,a) = (last,b) := GeneralNominalIdentities.pair_injective same
    exact ⟨congrArg Prod.fst pair,congrArg Prod.snd pair⟩
  · rintro ⟨rfl,rfl⟩; rfl

theorem clause_signature (valid : value.Signature roles) : (clause value).Signature roles := by
  refine ⟨valid.1,?_⟩
  intro output member
  obtain ⟨prior,present,rfl⟩ := List.mem_map.mp member
  exact valid.2 prior present

theorem declaration_checked (checked : DeclarationChecked constructors roles value) :
    DeclarationChecked constructors roles (declaration value) := by
  constructor
  · refine ⟨checked.signature.1,checked.signature.2.1,checked.signature.2.2.1,?_⟩
    intro next member
    obtain ⟨prior,present,rfl⟩ := List.mem_map.mp member
    exact clause_signature (checked.signature.2.2.2 prior present)
  · refine ⟨?_,checked.identified.2.1,checked.identified.2.2.1,?_,?_⟩
    · simpa [declaration,clause,List.map_map,Function.comp_def] using checked.identified.1
    · rw [outputNames]; exact checked.identified.2.2.2.1
    · intro next member
      obtain ⟨prior,present,rfl⟩ := List.mem_map.mp member
      have injective : Function.Injective (GeneralNominalIdentities.pair prior.id) :=
        fun _ _ same => (equation_key.mp same).2
      have unique := List.Pairwise.map (S := Ne) (GeneralNominalIdentities.pair prior.id)
        (fun _ _ distinct same => distinct (injective same)) (checked.identified.2.2.2.2 prior present)
      change List.Pairwise (fun a b => a ≠ b) _
      simpa only [clause,equation,List.map_map,Function.comp_def] using unique
  · intro next member
    obtain ⟨prior,present,rfl⟩ := List.mem_map.mp member
    obtain ⟨parent,visible,identity,output,within,key,rhs⟩ := checked.produced prior present
    refine ⟨clause parent,List.mem_map.mpr ⟨parent,visible,rfl⟩,identity,
      equation parent.id output,List.mem_map.mpr ⟨output,within,rfl⟩,?_,rhs⟩
    simp only [equation,binder,identity,key]
  · constructor
    · intro name named
      exact checked.outputOnly.1 name (outputNames value ▸ named)
    · intro next member name named
      obtain ⟨prior,present,rfl⟩ := List.mem_map.mp member
      exact checked.outputOnly.2 prior present name (outputNames value ▸ named)
  · refine ⟨?_,?_,?_⟩
    · intro next member
      obtain ⟨prior,present,rfl⟩ := List.mem_map.mp member
      exact checked.scope.1 prior present
    · intro output member name used
      rcases checked.scope.2.1 output member name used with found | found
      · exact Or.inl found
      · exact Or.inr ((outputNames value).symm ▸ found)
    · intro next member output within
      obtain ⟨prior,present,rfl⟩ := List.mem_map.mp member
      obtain ⟨original,found,rfl⟩ := List.mem_map.mp within
      simpa only [inputNames,outputNames,equation] using checked.scope.2.2 prior present original found
  · refine ⟨checked.constructorScoped.1,?_,checked.constructorScoped.2.2⟩
    intro next member
    obtain ⟨prior,present,rfl⟩ := List.mem_map.mp member
    refine ⟨(checked.constructorScoped.2.1 prior present).1,?_⟩
    intro output within
    obtain ⟨original,found,rfl⟩ := List.mem_map.mp within
    exact (checked.constructorScoped.2.1 prior present).2 original found
  · intro next member
    obtain ⟨prior,present,rfl⟩ := List.mem_map.mp member
    exact checked.countsCovered prior present
  · intro next member
    obtain ⟨prior,present,rfl⟩ := List.mem_map.mp member
    exact checked.paterson prior present
  · intro next member
    obtain ⟨prior,present,rfl⟩ := List.mem_map.mp member
    exact checked.conservative prior present
  · intro next member
    obtain ⟨prior,present,rfl⟩ := List.mem_map.mp member
    exact checked.captureStable prior present

theorem registry_checked (checked : Checked value) : Checked (registry value) := by
  constructor
  · simpa [registry,declaration,List.map_map,Function.comp_def] using checked.1
  · intro next member
    obtain ⟨prior,present,rfl⟩ := List.mem_map.mp member
    exact declaration_checked (checked.2 prior present)

theorem declaration_reorders (order : DeclarationReorders first last) :
    DeclarationReorders (declaration first) (declaration last) :=
  ⟨order.id,order.role,order.head,order.requirements.map clause,order.associated,
    congrArg (List.map binder) order.outputBinders⟩

theorem registry_reorders (order : Reorders first last) : Reorders (registry first) (registry last) := by
  obtain ⟨constructors,roles,middle,permutation,related⟩ := order
  refine ⟨constructors,roles,middle.map declaration,permutation.map declaration,?_⟩
  have mapped : ∀ xs ys, CommonRoleOutermostResolver.All₂ DeclarationReorders xs ys →
      CommonRoleOutermostResolver.All₂ DeclarationReorders (xs.map declaration) (ys.map declaration) := by
    intro xs ys pairs
    induction pairs with
    | nil => exact .nil
    | cons pair rest ih => exact .cons (declaration_reorders pair) ih
  exact mapped _ _ related

theorem declaration_coverage
    (covered : GeneralNominalCenteredHeadWFSource.DeclarationCovered constructors interpretation value) :
    GeneralNominalCenteredHeadWFSource.DeclarationCovered constructors interpretation (declaration value) := by
  refine ⟨covered.1,?_,covered.2.2⟩
  intro next member
  obtain ⟨prior,present,rfl⟩ := List.mem_map.mp member
  refine ⟨(covered.2.1 prior present).1,?_⟩
  intro output within
  obtain ⟨original,found,rfl⟩ := List.mem_map.mp within
  exact (covered.2.1 prior present).2 original found

theorem coverage (covered : GeneralNominalCenteredHeadWFSource.Coverage value interpretation) :
    GeneralNominalCenteredHeadWFSource.Coverage (registry value) interpretation := by
  refine ⟨?_,covered.2⟩
  intro next member
  obtain ⟨prior,present,rfl⟩ := List.mem_map.mp member
  exact declaration_coverage (covered.1 prior present)

theorem initial_source (source : GeneralNominalSourceFormation.InitialSource value context root) :
    GeneralNominalSourceFormation.InitialSource (registry value) context root :=
  ⟨source.roles_agree,source.metadata,source.linked,source.intervals,source.below_seed,source.unallocated⟩

end Yulang.GeneralNominalCenteredHeadAllocEncoding
