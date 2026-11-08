import Yulang.CommonRoleAssociatedStateFlow
import Yulang.CheckedRoles
import Yulang.RoleDictionaries

/-! A checked first-order Parent/Left/Right registry. Right's receiver is
already str; its declared output is int. This demonstrates an actual final
parent dictionary AFTER the associated value is computed, not a full open
source binding parser or a solution of the original unspecified example. -/
namespace Yulang.CommonRoleAssociatedParentGround
open Roles
open Roles.Examples (int str)
open Roles.AssocExamples (box singletonEnv)

def parent : Impl := ⟨20, [box (.var 0)], [⟨21, [.var 0]⟩, ⟨22, [str]⟩], 100⟩
def leftInt : Impl := ⟨21, [int], [], 101⟩
def leftStr : Impl := ⟨21, [str], [], 102⟩
def right : Impl := ⟨22, [str], [], 103⟩
def visible : List Impl := [parent, leftInt, leftStr, right]

theorem declarations_checked : CheckedRoles.checkDatabase visible = true := by decide +kernel

theorem declarations_wellFormed : WellFormed visible :=
  (CheckedRoles.checkDatabase_exact visible).mp declarations_checked

def rightAnnotation : AssocImpl := ⟨right, [(0, int)], by decide⟩
def annotations : List AssocImpl :=
  [⟨parent, [], by decide⟩, ⟨leftInt, [], by decide⟩,
    ⟨leftStr, [], by decide⟩, rightAnnotation]

def rightEnvironment : AssocEnv where
  impls := annotations
  coherent := by
    intro i hi j hj same
    simp only [annotations, List.mem_cons, List.not_mem_nil, or_false] at hi hj
    rcases hi with rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl <;>
      simp_all [parent, leftInt, leftStr, rightAnnotation, right]

theorem environment_cores : rightEnvironment.cores = visible := rfl

def rightSignature : RoleDecl where
  arity := 1
  assoc := fun name => if name = 0 then some none else none
  defaultsScoped := by intro name rhs h; split at h <;> simp_all

def noAssociated : RoleDecl where
  arity := 1
  assoc := fun _ => none
  defaultsScoped := by intro _ _ h; cases h

def rightRoles : RoleDecls := fun role => if role = 22 then rightSignature else noAssociated

theorem right_wellFormed : WellFormed rightEnvironment.cores :=
  environment_cores.symm ▸ declarations_wellFormed

theorem right_assocWellFormed : AssocWellFormed rightEnvironment rightRoles := by
  intro i member
  simp only [rightEnvironment, annotations, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;>
    simp [AssocHeadVars, AssocComplete, AssocDeclared, rightAnnotation, right,
      parent, leftInt, leftStr, rightRoles, rightSignature, noAssociated,
      int, box, Term.occurrences, argsOccurrences]

def rightGoal : Goal := ⟨22, [str]⟩

theorem right_resolved : resolve rightEnvironment.cores right_wellFormed rightGoal = .resolved := by
  rw [resolve_one _ _ _ right (by decide +kernel)]
  rfl

theorem right_value : assocOf rightEnvironment rightRoles right_wellFormed rightGoal 0 = some int := by
  rw [assoc_independent_of_constraints _ _ _ _ _ right_resolved rightAnnotation
    (by simp [rightEnvironment, annotations]) (by decide +kernel)]
  rfl

def request : CommonRoleAssociatedStateFlow.Request 1 := ⟨rightGoal, 0, 0⟩

theorem equation_from_declaration :
    CommonRoleAssociatedStateFlow.Computed rightEnvironment rightRoles right_wellFormed
      request .int := ⟨rfl, int, right_value, rfl⟩

def parentGoal (value : Term) : Goal := ⟨20, [box value]⟩

theorem left_int_resolved : resolve visible declarations_wellFormed ⟨21, [int]⟩ = .resolved := by
  rw [resolve_one _ _ _ leftInt (by decide +kernel)]
  rfl

theorem visible_right_resolved : resolve visible declarations_wellFormed rightGoal = .resolved := by
  rw [resolve_one _ _ _ right (by decide +kernel)]
  rfl

theorem parent_int_resolved : resolve visible declarations_wellFormed (parentGoal int) = .resolved := by
  rw [resolve_one _ _ _ parent (by decide +kernel)]
  change Roles.combine [resolve visible declarations_wellFormed ⟨21, [int]⟩,
    resolve visible declarations_wellFormed rightGoal] = .resolved
  rw [left_int_resolved, visible_right_resolved]
  rfl

/-- Associated declaration computation determines this known final parent goal.
No ordinary atom is supplied by the caller of this entry. -/
def finalParent : Option Result :=
  (assocOf rightEnvironment rightRoles right_wellFormed rightGoal 0).map
    fun value => resolve visible declarations_wellFormed (parentGoal value)

theorem final_parent_resolved : finalParent = some .resolved := by
  simp only [finalParent, right_value, Option.map_some, parent_int_resolved]

def finalDictionary : Option RoleDictionaries.Answer :=
  (assocOf rightEnvironment rightRoles right_wellFormed rightGoal 0).map
    fun value => RoleDictionaries.elaborate visible declarations_wellFormed (parentGoal value)

/-- The actual outer dictionary constructor succeeds; every retained declaration
belongs to this exact visible registry. This is the resulting ground goal only. -/
theorem final_dictionary_provenance :
    ∃ plan, finalDictionary = some (.resolved plan) ∧
      ∀ implementation ∈ plan.declarations, implementation ∈ visible := by
  let dictionary := RoleDictionaries.buildResolved visible declarations_wellFormed
    (parentGoal int) parent_int_resolved
  have success := (RoleDictionaries.elaborate_success_iff visible declarations_wellFormed
    (parentGoal int) dictionary.erase).mpr ⟨dictionary, rfl⟩
  refine ⟨dictionary.erase, ?_, dictionary.all_visible⟩
  simp only [finalDictionary, right_value, Option.map_some, success]

end Yulang.CommonRoleAssociatedParentGround
