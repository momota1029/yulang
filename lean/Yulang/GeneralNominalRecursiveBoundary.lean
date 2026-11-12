import Yulang.GeneralNominalRecursiveCandidates
import Yulang.GeneralNominalLocalBoundary

/-! The recursive inspection package extends the existing local boundary.
The four source transition/evidence obligations remain explicit. Legacy
emission interfaces retain their existing names and types. -/
namespace Yulang.GeneralNominalLocalBoundary

open GeneralNominalRecursiveCandidates
open GeneralDeclarations
open GeneralSourceDictionaries (Occurrence)
open CommonRoleOutermostResolver (Frontier)

def recursiveFields (roles : Roles.RoleDecls) : Fields (GeneralNominalCandidates.vocabulary roles) where
  Checked := fun registry => registry.roles = roles ∧ Checked registry
  Models := fun context => GeneralNominalState.Models context.state
  RootPending := fun _ context root => GeneralNominalState.RootPending context.state root.demand
  RootK2 := fun _ context root => GeneralNominalMixedRecurrence.RootK2 context.state root.demand
  CandidateK2 := GeneralNominalRecursiveCandidates.CandidateK2
  InspectionPending := GeneralNominalRecursiveCandidates.InspectionPending
  Survivor := GeneralNominalRecursiveCandidates.Survivor
  Reorders := GeneralRegistryReordering.Reorders
  DictionaryEquivalent := GeneralDictionaryPayloadOrder.Equivalent

theorem recursive_survivor_functional (roles : Roles.RoleDecls) (registry : Registry)
    (checked : (recursiveFields roles).Checked registry) (context : Context) (root : Occurrence roles) :
    SurvivorChildrenFunctional (recursiveFields roles) registry context root :=
  fun key first last one two => survivor_children_functional registry checked.2 context root key first last one two

theorem recursive_local_total (roles : Roles.RoleDecls) (registry : Registry)
    (checked : (recursiveFields roles).Checked registry) (context : Context) (root : Occurrence roles) :
    ∃ frontier, Local (recursiveFields roles) registry context root frontier :=
  local_total (recursive_survivor_functional roles registry checked context root)

theorem recursive_local_total_decidable (roles : Roles.RoleDecls) (registry : Registry)
    (checked : (recursiveFields roles).Checked registry) (context : Context) (root : Occurrence roles)
    [Decidable ((recursiveFields roles).RootPending registry context root)]
    [Decidable ((recursiveFields roles).RootK2 registry context root)]
    [Decidable ((recursiveFields roles).CandidateK2 registry context root)]
    [Decidable ((recursiveFields roles).InspectionPending registry context root)]
    [Decidable (∃ key children, (recursiveFields roles).Survivor registry context root key children)]
    [∀ key : Nat, Decidable (∃ key' children',
      (recursiveFields roles).Survivor registry context root key' children' ∧ key ≠ key')] :
    ∃ frontier, Local (recursiveFields roles) registry context root frontier :=
  local_total_decidable (recursive_survivor_functional roles registry checked context root)

theorem recursive_local_functional (roles : Roles.RoleDecls) (registry : Registry)
    (context : Context) (root : Occurrence roles) (first last : Frontier (Occurrence roles))
    (one : Local (recursiveFields roles) registry context root first)
    (two : Local (recursiveFields roles) registry context root last) : first = last :=
  local_functional one two

theorem recursive_local_extension (roles : Roles.RoleDecls) (registry : Registry)
    (context : Context) (root : Occurrence roles)
    (remaining : Remaining (GeneralNominalCandidates.vocabulary roles)) (frontier : Frontier (Occurrence roles)) :
    Local (recursiveFields roles) registry context root frontier ↔
      B4TargetV3.Local (complete (recursiveFields roles) remaining) registry context root frontier :=
  local_extension remaining frontier

theorem recursive_candidate_trichotomy (registry : Registry) (context : Context) (root : Occurrence roles)
    (ready : ¬ GeneralNominalState.RootPending context.state root.demand)
    (declaration : Declaration) (visible : declaration ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (sameRole : declaration.role = root.demand.role) :
    Failed registry context root declaration checked ∨ Prepared registry context root declaration checked ∨
      InspectionPending registry context root := by
  classical
  by_cases failed : Failed registry context root declaration checked
  · exact Or.inl failed
  by_cases prepared : Prepared registry context root declaration checked
  · exact Or.inr (Or.inl prepared)
  exact Or.inr (Or.inr ⟨ready,declaration,visible,checked,sameRole,failed,prepared⟩)

theorem recursive_failed_not_prepared (registry : Registry) (context : Context) (root : Occurrence roles)
    (declaration : Declaration) (checked : DeclarationChecked registry.constructors roles declaration)
    (failed : Failed registry context root declaration checked) : ¬ Prepared registry context root declaration checked := by
  rintro ⟨_,_,_,bounds,located,finished,_,consistent⟩
  obtain ⟨_,_,other,found,_,_,reason⟩ := failed
  have same := Option.some.inj (located.symm.trans found)
  subst other
  rcases reason with conflict | inconsistent
  · exact conflict finished.2.1
  · exact inconsistent.2 consistent

theorem recursive_candidateK2_rejects (roles : Roles.RoleDecls) (registry : Registry)
    (context : Context) (root : Occurrence roles)
    (cycle : CandidateK2 registry context root) : Local (recursiveFields roles) registry context root .rejected :=
  .rejected ⟨cycle.1,Or.inr (Or.inl cycle)⟩

theorem recursive_pending_excludes_candidates (roles : Roles.RoleDecls) (registry : Registry)
    (context : Context) (root : Occurrence roles)
    (pending : GeneralNominalState.RootPending context.state root.demand) :
    (∀ key children, ¬ (recursiveFields roles).Survivor registry context root key children) ∧
      ¬ (recursiveFields roles).InspectionPending registry context root ∧
      ¬ (recursiveFields roles).CandidateK2 registry context root ∧
      ¬ (recursiveFields roles).RootK2 registry context root :=
  ⟨fun _ _ survivor => survivor.1 pending,fun inspecting => inspecting.1 pending,
    fun cycle => cycle.1 pending,fun cycle => cycle.2.1 pending⟩

end Yulang.GeneralNominalLocalBoundary
