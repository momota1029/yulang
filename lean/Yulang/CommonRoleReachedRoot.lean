import Yulang.CommonRoleRegularResolutionObstruction

/-!
# Reached-root rejection, on an explicit finite counterexample grammar

This is an E2 test fragment, not a replacement for the full Common language.
Its finite descriptions contain finite int/pair/variant trees, arbitrary
finite constructor contexts, and the one-node graph μ = variant 7 μ.
The only structural cyclic component is that variant-only graph. A pair
context cannot point back to itself. `clockOnly` also recognizes finite
unrollings of the graph, so rejection is unchanged by those unrollings.

Evidence reads actual unary `Roles.Impl` head and where fields. Reaching
means invoking the dictionary judgment at its root or at a where child;
looking at a nested type during head matching is not a resolution invocation.
All children use the same visible declarations and evidence is finite.
-/

namespace Yulang.CommonRoleReachedRoot

open CommonRoleLinearClock (Pattern Ground)

inductive Description where
  | finite : Ground → Description
  | data : CommonRoleComputation.Tree → Description
  | clock
  | pair : Description → Description → Description
  | variant : Nat → Description → Description
  deriving DecidableEq, Repr

def Description.eval : Description → Common.Ty
  | .finite value => value.eval
  | .data value => value.encode.eval
  | .clock => CommonRoleLinearClock.clock
  | .pair first last => Common.pair first.eval last.eval
  | .variant tag payload => Common.variant tag payload.eval

/-- In this grammar the root belongs to a cyclic structural component
exactly when the description is a finite unrolling of the variant clock.
In particular this does not search for cycles below a pair root. -/
def Description.clockOnly : Description → Bool
  | .clock => true
  | .variant tag payload => (tag == 7) && payload.clockOnly
  | _ => false

def StructuralRecursive (type : Description) : Prop := type.clockOnly = true

theorem clock_rejected : StructuralRecursive .clock := rfl

theorem pair_not_recursive (first last : Description) :
    ¬ StructuralRecursive (.pair first last) := by
  simp [StructuralRecursive, Description.clockOnly]

theorem finite_not_recursive (value : Ground) :
    ¬ StructuralRecursive (.finite value) := by
  simp [StructuralRecursive, Description.clockOnly]

theorem recursive_unrolling (type : Description) :
    StructuralRecursive (.variant 7 type) ↔ StructuralRecursive type := by
  simp [StructuralRecursive, Description.clockOnly]

def instantiate (pattern : Pattern) (assignment : Nat → Description) : Description :=
  match pattern with
  | .var name => assignment name
  | .int => .finite .int
  | .pair first last => .pair (instantiate first assignment) (instantiate last assignment)
  | .variant tag payload => .variant tag (instantiate payload assignment)

theorem instantiate_eval (pattern : Pattern) (assignment : Nat → Description) :
    (instantiate pattern assignment).eval = pattern.eval (fun name => (assignment name).eval) := by
  induction pattern <;> simp_all [instantiate, Description.eval, Pattern.eval, Ground.eval]

def interpretTerm (term : Roles.Term) (assignment : Nat → Description) : Option Description :=
  (CommonRoleLinearRepresentation.decodePattern term).map (fun pattern => instantiate pattern assignment)

@[simp] theorem interpretTerm_encode (pattern : Pattern) (assignment : Nat → Description) :
    interpretTerm pattern.encode assignment = some (instantiate pattern assignment) := by
  simp [interpretTerm, CommonRoleLinearRepresentation.decodePattern_encode]

structure Goal where
  role : Nat
  argument : Description
  deriving DecidableEq, Repr

def interpretGoal (requirement : Roles.Goal) (assignment : Nat → Description) : Option Goal := do
  let [argument] := requirement.args | none
  return ⟨requirement.role, ← interpretTerm argument assignment⟩

def Equivalent (first last : Goal) : Prop :=
  first.role = last.role ∧ Common.Equivalent first.argument.eval last.argument.eval

def Matches (implementation : Roles.Impl) (goal : Goal) (assignment : Nat → Description) : Prop :=
  ∃ head, interpretGoal ⟨implementation.role, implementation.head⟩ assignment = some head ∧
    Equivalent head goal

def Unique (visible : List Roles.Impl) (implementation : Roles.Impl) (goal : Goal) : Prop :=
  ∀ other ∈ visible, (∃ assignment, Matches other goal assignment) → other = implementation

mutual
  inductive Derives (visible : List Roles.Impl) : Goal → Prop where
    | impl {goal : Goal} (safe : ¬ StructuralRecursive goal.argument)
        (implementation : Roles.Impl) (assignment : Nat → Description)
        (member : implementation ∈ visible) (matched : Matches implementation goal assignment)
        (children : DerivesChildren visible assignment implementation.constraints) : Derives visible goal

  inductive DerivesChildren (visible : List Roles.Impl) :
      (Nat → Description) → List Roles.Goal → Prop where
    | nil {assignment} : DerivesChildren visible assignment []
    | cons {assignment} (requirement : Roles.Goal) (child : Goal) (rest : List Roles.Goal)
        (interpreted : interpretGoal requirement assignment = some child)
        (derivation : Derives visible child) (children : DerivesChildren visible assignment rest) :
        DerivesChildren visible assignment (requirement :: rest)
end

mutual
  inductive Dictionary (visible : List Roles.Impl) : Goal → Type where
    | impl {goal : Goal} (safe : ¬ StructuralRecursive goal.argument)
        (implementation : Roles.Impl) (assignment : Nat → Description)
        (member : implementation ∈ visible) (matched : Matches implementation goal assignment)
        (unique : Unique visible implementation goal)
        (children : Children visible assignment implementation.constraints) : Dictionary visible goal

  inductive Children (visible : List Roles.Impl) :
      (Nat → Description) → List Roles.Goal → Type where
    | nil {assignment} : Children visible assignment []
    | cons {assignment} (requirement : Roles.Goal) (child : Goal) (rest : List Roles.Goal)
        (interpreted : interpretGoal requirement assignment = some child)
        (dictionary : Dictionary visible child) (children : Children visible assignment rest) :
        Children visible assignment (requirement :: rest)
end

mutual
  def Dictionary.erase {visible : List Roles.Impl} {goal : Goal} :
      Dictionary visible goal → RoleDictionaries.Plan
    | .impl _ implementation _ _ _ _ children => .node implementation children.erase

  def Children.erase {visible : List Roles.Impl} {assignment : Nat → Description}
      {requirements : List Roles.Goal} : Children visible assignment requirements → List RoleDictionaries.Plan
    | .nil => []
    | .cons _ _ _ _ dictionary children => dictionary.erase :: children.erase
end

theorem Dictionary.derives {visible : List Roles.Impl} {goal : Goal}
    (dictionary : Dictionary visible goal) : Derives visible goal := by
  induction dictionary using Dictionary.rec (motive_2 := fun assignment requirements _ =>
    DerivesChildren visible assignment requirements) with
  | impl safe implementation assignment member matched unique children ih =>
      exact .impl safe implementation assignment member matched ih
  | nil => exact .nil
  | cons requirement child rest interpreted dictionary children ihChild ihRest =>
      exact .cons requirement child rest interpreted ihChild ihRest

/-- A rejection is a separate outcome. The path records the selected actual
implementation and the where index at each descent. Head overlap is checked
before descending, just as in the earlier independent dictionary semantics. -/
inductive Rejects (visible : List Roles.Impl) : Goal → List (Roles.Impl × Nat) → Prop where
  | here {goal} (recursive : StructuralRecursive goal.argument) : Rejects visible goal []
  | descend {goal child path} (safe : ¬ StructuralRecursive goal.argument)
      (implementation : Roles.Impl) (assignment : Nat → Description) (index : Nat)
      (member : implementation ∈ visible) (matched : Matches implementation goal assignment)
      (unique : Unique visible implementation goal) (requirement : Roles.Goal)
      (present : implementation.constraints[index]? = some requirement)
      (interpreted : interpretGoal requirement assignment = some child)
      (rejected : Rejects visible child path) :
      Rejects visible goal ((implementation, index) :: path)

theorem recursive_has_no_dictionary (visible : List Roles.Impl) (goal : Goal)
    (recursive : StructuralRecursive goal.argument) : ¬ Nonempty (Dictionary visible goal) := by
  rintro ⟨dictionary⟩
  cases dictionary with
  | impl safe => exact safe recursive

theorem Dictionary.all_visible {visible : List Roles.Impl} {goal : Goal}
    (dictionary : Dictionary visible goal) :
    ∀ implementation ∈ dictionary.erase.declarations, implementation ∈ visible := by
  induction dictionary using Dictionary.rec (motive_2 := fun _ _ children =>
    ∀ implementation ∈ children.erase.flatMap RoleDictionaries.Plan.declarations,
      implementation ∈ visible) with
  | impl safe implementation assignment member matched unique children ih =>
      intro wanted present
      simp only [Dictionary.erase, RoleDictionaries.Plan.declarations, List.mem_cons] at present
      exact present.elim (fun same => same ▸ member) (ih wanted)
  | nil => contradiction
  | cons requirement child rest interpreted dictionary children ihChild ihRest =>
      rename_i wanted present
      simp only [Children.erase, List.flatMap_cons, List.mem_append] at present
      exact present.elim (ihChild wanted) (ihRest wanted)

end Yulang.CommonRoleReachedRoot
