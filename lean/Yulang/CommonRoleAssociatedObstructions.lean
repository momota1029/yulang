import Yulang.CheckedRoles
import Yulang.RoleDictionaries
import Yulang.CommonRecord
import Yulang.CommonRigidHeadInspection

/-!
# Associated types are not determined by syntactic head occurrence

All inputs below are finite, row-free, nonrecursive types. The one declaration
has head `{x : int, x : a}` and associated body `a`, with no where conditions.
It passes the existing declaration and associated-type well-formedness checks.
The first-field-wins equation erases the only occurrence of `a` from the head's
Common meaning. Two actual first-order associated derivations therefore have
equivalent Common heads and inequivalent associated results.

This is an obstruction to preserving those independent associated derivations
while matching heads modulo Common equivalence. It is not a termination or
undecidability claim, and it does not introduce a new declaration rejection
policy. No arbitrary decoder or semantic role oracle is used.
-/

namespace Yulang.CommonRoleAssociatedObstructions

open Common (Ty Equivalent)

/-- A finite source-type fragment with fixed constructor meanings. In
particular, no general union annotation or arbitrary semantic row occurs. -/
inductive Pattern where
  | var : Nat → Pattern
  | int | bool | empty
  | record : Nat → Pattern → Pattern → Pattern
  deriving DecidableEq, Repr

/-- Constructor identities 0/1/2 mean int/bool/empty record; 3+l is a field l.
These are an encoding of this explicit grammar, not a decoder of Common types. -/
def Pattern.encode : Pattern → Roles.Term
  | .var name => .var name
  | .int => .app 0 []
  | .bool => .app 1 []
  | .empty => .app 2 []
  | .record label payload rest => .app (3 + label) [payload.encode, rest.encode]

def Pattern.eval (assignment : Nat → Ty) : Pattern → Ty
  | .var name => assignment name
  | .int => .base .int
  | .bool => .base .bool
  | .empty => Common.emptyRecord
  | .record label payload rest =>
      Common.record label (payload.eval assignment) (rest.eval assignment)

def headPattern : Pattern := .record 0 .int (.record 0 (.var 0) .empty)
def rhsPattern : Pattern := .var 0
def goalPattern : Pattern := .record 0 .int .empty
def closedGoal : Ty := goalPattern.eval (fun _ => .bottom)

def implementation : Roles.Impl := ⟨0, [headPattern.encode], [], 0⟩
def annotated : Roles.AssocImpl :=
  ⟨implementation, [(0, rhsPattern.encode)], by decide⟩
def environment : Roles.AssocEnv := Roles.AssocExamples.singletonEnv annotated

def roleDeclaration : Roles.RoleDecl where
  arity := 1
  assoc := fun name => if name = 0 then some none else none
  defaultsScoped := by
    intro name rhs equality
    split at equality <;> simp_all

def roles : Roles.RoleDecls := fun _ => roleDeclaration

theorem declaration_accepted : CheckedRoles.checkDatabase environment.cores = true := by
  decide +kernel

theorem declaration_wellFormed : Roles.WellFormed environment.cores :=
  (CheckedRoles.checkDatabase_exact _).mp declaration_accepted

theorem associated_wellFormed : Roles.AssocWellFormed environment roles := by
  intro i member
  have same : i = annotated := by simpa [environment, Roles.AssocExamples.singletonEnv] using member
  subst i
  constructor
  · intro name rhs body v occurs
    have bodyEq : (name, rhs) = (0, rhsPattern.encode) := by simpa [annotated] using body
    cases bodyEq
    simp only [rhsPattern, Pattern.encode, Roles.Term.occurrences] at occurs
    have eq : v = 0 := by split at occurs <;> omega
    subst v
    decide +kernel
  · constructor
    · constructor
      · rfl
      · intro name default declared
        have eq : name = 0 := by
          by_cases same : name = 0
          · exact same
          · simp [roles, roleDeclaration, same] at declared
        subst name
        exact Or.inl ⟨rhsPattern.encode, rfl⟩
    · intro name rhs body
      have bodyEq : (name, rhs) = (0, rhsPattern.encode) := by simpa [annotated] using body
      cases bodyEq
      exact ⟨none, rfl⟩

/-- An arbitrary Common assignment, including arbitrary regular types, loses
the associated variable when the head is interpreted. -/
theorem every_head_instance (assignment : Nat → Ty) :
    Equivalent (headPattern.eval assignment) closedGoal :=
  Common.common_shadowed_head_equivalent 0 (.base .int) (assignment 0) Common.emptyRecord

theorem int_not_bool : ¬ Equivalent (.base .int) (.base .bool) := by
  intro same
  have impossible := (CommonRigidHeadInspection.base_iff .int .bool).mp same.1
  cases impossible

/-- No selected associated type, even noncomputably chosen, can agree with
all matching substitutions of this accepted declaration at this finite goal. -/
theorem no_associated_value_agrees :
    ¬ ∃ selected : Ty, ∀ assignment : Nat → Ty,
      Equivalent (headPattern.eval assignment) closedGoal →
      Equivalent selected (rhsPattern.eval assignment) := by
  rintro ⟨selected, agrees⟩
  have first := agrees (fun _ => .base .int) (every_head_instance _)
  have last := agrees (fun _ => .base .bool) (every_head_instance _)
  exact int_not_bool (Common.equivalent_trans (Common.equivalent_symm first) last)

def groundHead (hidden : Pattern) : Pattern :=
  .record 0 .int (.record 0 hidden .empty)

def rigidGoal (hidden : Pattern) : Roles.Goal := ⟨0, [(groundHead hidden).encode]⟩

/-- The witnesses below use the actual old head matcher, with no new oracle. -/
theorem first_order_selected (hidden : Pattern) :
    Roles.candidates environment.cores (rigidGoal hidden) = [implementation] := by
  have matched : Roles.headMatches implementation (rigidGoal hidden) = true :=
    (Roles.matches_iff _ _).mpr ⟨rfl, (fun _ => hidden.encode), rfl⟩
  change Roles.candidates [implementation] (rigidGoal hidden) = [implementation]
  simp [Roles.candidates, Roles.distinct, matched]

theorem first_order_resolved (hidden : Pattern) :
    Roles.resolve environment.cores declaration_wellFormed (rigidGoal hidden) = .resolved := by
  rw [Roles.resolve_one _ _ _ implementation (first_order_selected hidden)]
  rfl

theorem first_order_associated (hidden : Pattern) :
    Roles.assocOf environment roles declaration_wellFormed (rigidGoal hidden) 0 =
      some hidden.encode := by
  exact Roles.assoc_explicit_eq environment roles declaration_wellFormed
    associated_wellFormed (rigidGoal hidden) 0 (first_order_resolved hidden)
    annotated (by simp [environment, Roles.AssocExamples.singletonEnv])
    (first_order_selected hidden) (fun _ => hidden.encode) rfl rhsPattern.encode rfl

/-- This is an existing independent `Roles.AssocDerives` proof, not an
associated relation defined to coincide with a new solver. -/
theorem first_order_derivation (hidden : Pattern) :
    Roles.AssocDerives environment roles (rigidGoal hidden) 0 hidden.encode := by
  apply Roles.AssocDerives.explicit annotated (fun _ => hidden.encode)
    (by simp [environment, Roles.AssocExamples.singletonEnv]) rfl rfl
    (fun _ member => False.elim (by simp [annotated, implementation] at member))
    rhsPattern.encode rfl

def firstOrderDictionary (hidden : Pattern) :
    RoleDictionaries.Dictionary environment.cores (rigidGoal hidden) :=
  .impl implementation (first_order_selected hidden)
    (fun _ member => False.elim (by simp [implementation] at member))

theorem first_order_dictionary_plan (hidden : Pattern) :
    (firstOrderDictionary hidden).erase = .node implementation [] := rfl

/-- The genuine two old goals have the same Common interpretation. This is
not a choice of a decoder identifying two unrelated constructor identities. -/
theorem ground_head_equivalent (hidden : Pattern) (assignment : Nat → Ty) :
    Equivalent ((groundHead hidden).eval assignment) closedGoal :=
  Common.common_shadowed_head_equivalent 0 (.base .int) (hidden.eval assignment) Common.emptyRecord

/-- Already two *finite ground* substitutions suffice. Arbitrary regular
types or arbitrary row predicates are not needed for the contradiction. -/
theorem finite_ground_associated_conflict :
    Roles.AssocDerives environment roles (rigidGoal .int) 0 Pattern.int.encode ∧
    Roles.AssocDerives environment roles (rigidGoal .bool) 0 Pattern.bool.encode ∧
    Equivalent ((groundHead .int).eval (fun _ => .bottom)) closedGoal ∧
    Equivalent ((groundHead .bool).eval (fun _ => .bottom)) closedGoal ∧
    ¬ Equivalent (Pattern.int.eval (fun _ => .bottom)) (Pattern.bool.eval (fun _ => .bottom)) :=
  ⟨first_order_derivation .int, first_order_derivation .bool,
    ground_head_equivalent .int _, ground_head_equivalent .bool _, int_not_bool⟩

end Yulang.CommonRoleAssociatedObstructions
