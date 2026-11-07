import Yulang.CommonRoleAssociatedObstructions
import Yulang.CommonRoleHeadDetermination

/-!
# Hidden head variables can change a recursively selected dictionary

The associated RHSs in this example are all the constant int. The accepted
semantic associated-head condition therefore does not remove this example.
The root's hidden variable is used only in a where child. Two actual successful
queries have Common-equivalent heads and different complete dictionary trees.
This module does not assert a K2 termination or undecidability result.
-/

namespace Yulang.CommonRoleWhereObstructions

open CommonRoleAssociatedObstructions (Pattern headPattern groundHead rigidGoal)
open Roles (Impl Goal)
open RoleDictionaries (Dictionary Plan)

def requirement : Goal := ⟨1, [Pattern.var 0 |>.encode]⟩
def rootImpl : Impl := ⟨0, [headPattern.encode], [requirement], 0⟩
def intImpl : Impl := ⟨1, [Pattern.int.encode], [], 1⟩
def boolImpl : Impl := ⟨1, [Pattern.bool.encode], [], 2⟩
def visible : List Impl := [rootImpl, intImpl, boolImpl]

theorem declarations_accepted : CheckedRoles.checkDatabase visible = true := by
  decide +kernel

theorem declarations_wellFormed : Roles.WellFormed visible :=
  (CheckedRoles.checkDatabase_exact visible).mp declarations_accepted

theorem root_sizes :
    Roles.argsSize rootImpl.head = 5 ∧ Roles.argsSize requirement.args = 1 := by
  decide +kernel

def intDictionary : Dictionary visible (rigidGoal .int) :=
  .impl rootImpl (by decide +kernel) (fun child member => by
    have same : child = requirement := by simpa [rootImpl] using member
    subst child
    change Dictionary visible ⟨1, [Pattern.int.encode]⟩
    exact .impl intImpl (by decide +kernel)
      (fun _ impossible => False.elim (by simp [intImpl] at impossible)))

def boolDictionary : Dictionary visible (rigidGoal .bool) :=
  .impl rootImpl (by decide +kernel) (fun child member => by
    have same : child = requirement := by simpa [rootImpl] using member
    subst child
    change Dictionary visible ⟨1, [Pattern.bool.encode]⟩
    exact .impl boolImpl (by decide +kernel)
      (fun _ impossible => False.elim (by simp [boolImpl] at impossible)))

def intPlan : Plan := .node rootImpl [.node intImpl []]
def boolPlan : Plan := .node rootImpl [.node boolImpl []]

theorem int_dictionary_plan : intDictionary.erase = intPlan := rfl
theorem bool_dictionary_plan : boolDictionary.erase = boolPlan := rfl

theorem actual_int_elaboration :
    RoleDictionaries.elaborate visible declarations_wellFormed (rigidGoal .int) =
      .resolved intPlan :=
  (RoleDictionaries.elaborate_success_iff _ _ _ _).mpr ⟨intDictionary, int_dictionary_plan⟩

theorem actual_bool_elaboration :
    RoleDictionaries.elaborate visible declarations_wellFormed (rigidGoal .bool) =
      .resolved boolPlan :=
  (RoleDictionaries.elaborate_success_iff _ _ _ _).mpr ⟨boolDictionary, bool_dictionary_plan⟩

theorem plans_differ : intPlan ≠ boolPlan := by
  intro same
  have children := (Plan.node.inj same).2
  have leaf := (List.cons.inj children).1
  have implementation := (Plan.node.inj leaf).1
  have key := congrArg Impl.key implementation
  change 1 = 2 at key
  omega

/-- Add a real, declared, non-vacuous associated RHS to every implementation.
Its value is constant and has no dependence on the hidden where variable. -/
def annotate (implementation : Impl) : Roles.AssocImpl :=
  ⟨implementation, [(0, Pattern.int.encode)], by decide⟩

def environment : Roles.AssocEnv where
  impls := visible.map annotate
  coherent := by
    intro first firstMember last lastMember _
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp firstMember
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp lastMember
    rfl

theorem environment_cores : environment.cores = visible := rfl

def roleDeclarations : List Roles.RoleDecl :=
  [CommonRoleAssociatedObstructions.roleDeclaration, CommonRoleAssociatedObstructions.roleDeclaration]

def roles : Roles.RoleDecls := fun name =>
  (roleDeclarations[name]?).getD CommonRoleAssociatedObstructions.undeclaredRole

theorem associated_wellFormed : Roles.AssocWellFormed environment roles := by
  intro annotated member
  change annotated ∈ visible.map annotate at member
  obtain ⟨implementation, present, equality⟩ := List.mem_map.mp member
  subst annotated
  constructor
  · intro name rhs body v occurs
    have pair : (name, rhs) = (0, Pattern.int.encode) := by simpa [annotate] using body
    cases pair
    simp [Pattern.encode, Roles.Term.occurrences, Roles.argsOccurrences] at occurs
  · have memberCases : implementation = rootImpl ∨ implementation = intImpl ∨ implementation = boolImpl := by
      simpa [visible] using present
    rcases memberCases with rfl | rfl | rfl
    all_goals
      constructor
      · constructor
        · rfl
        · intro name default declared
          have eq : name = 0 := by
            by_cases same : name = 0
            · exact same
            · simp [roles, roleDeclarations, annotate, rootImpl, intImpl, boolImpl,
                CommonRoleAssociatedObstructions.roleDeclaration, same] at declared
          subst name
          exact Or.inl ⟨Pattern.int.encode, rfl⟩
      · intro name rhs body
        have pair : (name, rhs) = (0, Pattern.int.encode) := by simpa [annotate] using body
        cases pair
        exact ⟨none, rfl⟩

open CommonRoleHeadDetermination (Declaration)

def rootDeclaration : Declaration :=
  ⟨0, 0, [headPattern], [(1, [.var 0])], [(0, .int)]⟩
def intDeclaration : Declaration := ⟨1, 1, [.int], [], [(0, .int)]⟩
def boolDeclaration : Declaration := ⟨1, 2, [.bool], [], [(0, .int)]⟩
def declarations : List Declaration := [rootDeclaration, intDeclaration, boolDeclaration]

/-- The new finite declarations compile to exactly the visible set already
used by both real dictionary constructions. -/
theorem encoded_declarations : declarations.map Declaration.toImpl = visible := rfl

theorem encoded_associated_bodies :
    declarations.map (fun declaration =>
      declaration.associated.map (fun pair => (pair.1, pair.2.encode))) =
      environment.impls.map Roles.AssocImpl.assoc := rfl

theorem associated_checker_accepts : CommonRoleHeadDetermination.checkRegistry declarations = true := by
  decide +kernel

/-- The approved condition is proved for all Common substitutions by the
real declaration checker, not supplied as a resolver-success hypothesis. -/
theorem head_determines_associated :
    CommonRoleHeadDetermination.RegistryHeadDeterminesAssociated declarations :=
  CommonRoleHeadDetermination.checkRegistry_sound declarations associated_checker_accepts

theorem combined_declaration_check_accepts : declarations.all Declaration.check = true := by
  decide +kernel

theorem each_declaration_verified (declaration : Declaration)
    (member : declaration ∈ declarations) :
    (CommonRoleHeadDetermination.verify declaration).isSome = true :=
  (CommonRoleHeadDetermination.verify_isSome_iff declaration).mpr
    (List.all_eq_true.mp combined_declaration_check_accepts declaration member)

theorem root_associated_is_int (goal : Roles.Goal)
    (success : Roles.resolve visible declarations_wellFormed goal = .resolved)
    (selected : Roles.candidates visible goal = [rootImpl]) :
    Roles.assocOf environment roles (environment_cores.symm ▸ declarations_wellFormed)
      goal 0 = some Pattern.int.encode := by
  exact Roles.assoc_explicit_eq environment roles
    (environment_cores.symm ▸ declarations_wellFormed) associated_wellFormed goal 0
    success (annotate rootImpl) (by simp [environment, visible]) selected
    (Roles.matchingSubst rootImpl.head goal.args)
    (Roles.matched_head ((Roles.mem_candidates.mp (selected ▸ List.mem_singleton_self rootImpl)).2))
    Pattern.int.encode rfl

theorem root_goals_equivalent :
    Common.Equivalent ((groundHead .int).eval (fun _ => .bottom))
      ((groundHead .bool).eval (fun _ => .bottom)) :=
  Common.equivalent_trans (CommonRoleAssociatedObstructions.ground_head_equivalent .int _)
    (Common.equivalent_symm (CommonRoleAssociatedObstructions.ground_head_equivalent .bool _))

/-- Unlike its constant associated RHS, this declaration's where argument
is not determined by the meaning of its head. -/
theorem where_argument_not_determined :
    ¬ CommonRoleHeadDetermination.HeadDeterminesAssociated [headPattern] [.var 0] :=
  CommonRoleHeadDetermination.Examples.hidden_associated_not_determined

end Yulang.CommonRoleWhereObstructions
