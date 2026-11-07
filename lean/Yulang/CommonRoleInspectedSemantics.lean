import Yulang.CommonRoleReachedRootObstruction
import Yulang.CommonRoleHeadDetermination

/-!
# Constructor-inspection rejection: independent E2 countergrammar

The fixed finite grammar extends int/pair/variant with empty records and one
field name, 0. Duplicate fields have the authoritative first-field-wins Common
meaning. The sole cyclic graph is μ = variant 7 μ. This is a countergrammar
for a universal E2 claim, not an E1 restriction of the target language.

Rejection has priority over ambiguity: a forbidden inspection by any visible
same-role head prevents selection and ambiguity. The separate design question
records that working choice. The counterfamily below is entirely finite, so
the obstruction does not depend on that priority.
-/

namespace Yulang.CommonRoleInspectedSemantics

open CommonRoleLinearClock (Ground)

inductive Pattern where
  | var : Nat → Pattern
  | int | empty
  | pair : Pattern → Pattern → Pattern
  | variant : Nat → Pattern → Pattern
  | record : Pattern → Pattern → Pattern
  deriving DecidableEq, Repr

def Pattern.encode : Pattern → Roles.Term
  | .var name => .var name
  | .int => .app 0 []
  | .empty => .app 2 []
  | .pair first last => .app 1 [first.encode, last.encode]
  | .variant tag payload => .app (tag + 3) [payload.encode]
  | .record payload rest => .app 3 [payload.encode, rest.encode]

def Pattern.eval (assignment : Nat → Common.Ty) : Pattern → Common.Ty
  | .var name => assignment name
  | .int => .base .int
  | .empty => Common.emptyRecord
  | .pair first last => Common.pair (first.eval assignment) (last.eval assignment)
  | .variant tag payload => Common.variant tag (payload.eval assignment)
  | .record payload rest => Common.record 0 (payload.eval assignment) (rest.eval assignment)

def liftPattern : CommonRoleLinearClock.Pattern → Pattern
  | .var name => .var name
  | .int => .int
  | .pair first last => .pair (liftPattern first) (liftPattern last)
  | .variant tag payload => .variant tag (liftPattern payload)

theorem lift_eval (pattern : CommonRoleLinearClock.Pattern) (assignment : Nat → Common.Ty) :
    (liftPattern pattern).eval assignment = pattern.eval assignment := by
  induction pattern <;> simp_all [liftPattern, Pattern.eval, CommonRoleLinearClock.Pattern.eval]

def decodePattern : Roles.Term → Option Pattern
  | .var name => some (.var name)
  | .app 0 [] => some .int
  | .app 2 [] => some .empty
  | .app 1 [first, last] => do return .pair (← decodePattern first) (← decodePattern last)
  | .app 3 [payload, rest] => do return .record (← decodePattern payload) (← decodePattern rest)
  | .app (tag + 3) [payload] => do return .variant tag (← decodePattern payload)
  | _ => none

@[simp] theorem decode_encode (pattern : Pattern) : decodePattern pattern.encode = some pattern := by
  induction pattern <;> simp [Pattern.encode, decodePattern, *]

def interpretTerm (term : Roles.Term) (assignment : Nat → Common.Ty) : Option Common.Ty :=
  (decodePattern term).map (fun pattern => pattern.eval assignment)

@[simp] theorem interpret_encode (pattern : Pattern) (assignment : Nat → Common.Ty) :
    interpretTerm pattern.encode assignment = some (pattern.eval assignment) := by
  simp [interpretTerm]

inductive Description where
  | int | empty | clock
  | ground : Ground → Description
  | data : CommonRoleComputation.Tree → Description
  | pair : Description → Description → Description
  | variant : Nat → Description → Description
  | record : Description → Description → Description
  deriving DecidableEq, Repr

def Description.eval : Description → Common.Ty
  | .int => .base .int
  | .empty => Common.emptyRecord
  | .clock => CommonRoleLinearClock.clock
  | .ground value => value.eval
  | .data value => value.encode.eval
  | .pair first last => Common.pair first.eval last.eval
  | .variant tag payload => Common.variant tag payload.eval
  | .record payload rest => Common.record 0 payload.eval rest.eval

def Description.finite : Description → Bool
  | .clock => false
  | .pair first last | .record first last => first.finite && last.finite
  | .variant _ payload => payload.finite
  | _ => true

def Description.recursiveRoot : Description → Bool
  | .clock => true
  | .variant tag payload => (tag == 7) && payload.recursiveRoot
  | _ => false

theorem finite_root (type : Description) (finite : type.finite = true) : type.recursiveRoot = false := by
  induction type <;> simp_all [Description.finite, Description.recursiveRoot]

inductive View where
  | int | empty | clock
  | pair : Description → Description → View
  | variant : Nat → Description → View
  | record : Description → Description → View

def Description.view : Description → View
  | .int | .ground .int | .data .leaf => .int
  | .empty => .empty
  | .clock => .clock
  | .ground (.pair first last) => .pair (.ground first) (.ground last)
  | .data (.node first last) => .pair (.data first) (.data last)
  | .pair first last => .pair first last
  | .ground (.variant tag payload) => .variant tag (.ground payload)
  | .variant tag payload => .variant tag payload
  | .record payload rest => .record payload rest

def View.Finite : View → Prop
  | .clock => False
  | .pair first last | .record first last => first.finite = true ∧ last.finite = true
  | .variant _ payload => payload.finite = true
  | _ => True

theorem finite_view (type : Description) (finite : type.finite = true) : type.view.Finite := by
  cases type with
  | ground value => cases value <;> trivial
  | data value => cases value <;> trivial
  | pair first last | record first last => exact Bool.and_eq_true_iff.mp finite
  | variant tag payload => exact finite
  | clock => contradiction
  | int | empty => trivial

/-- Remove explicitly shadowed fields before deciding which payloads a head
must inspect. This is inspection semantics, not the declaration size checker. -/
def Pattern.visible (hidden : Bool) : Pattern → Pattern
  | .record payload rest =>
      if hidden then rest.visible true else .record (payload.visible false) (rest.visible true)
  | .pair first last => .pair (first.visible false) (last.visible false)
  | .variant tag payload => .variant tag (payload.visible false)
  | pattern => pattern

def blockedRaw : Pattern → Description → Bool
  | .var _, _ => false
  | .int, type | .empty, type => type.recursiveRoot
  | .pair first last, type => type.recursiveRoot ||
      match type.view with
      | .pair a b => blockedRaw first a || blockedRaw last b
      | _ => false
  | .variant tag payload, type => type.recursiveRoot ||
      match type.view with
      | .variant other child => if tag = other then blockedRaw payload child else false
      | _ => false
  | .record payload rest, type => type.recursiveRoot ||
      match type.view with
      | .record a b => blockedRaw payload a || blockedRaw rest b
      | _ => false

theorem finite_not_blocked_raw (pattern : Pattern) (type : Description) (finite : type.finite = true) :
    blockedRaw pattern type = false := by
  induction pattern generalizing type with
  | var name => rfl
  | int | empty => exact finite_root type finite
  | pair first last ihFirst ihLast | record first last ihFirst ihLast =>
      simp only [blockedRaw, finite_root type finite, Bool.false_or]
      have children := finite_view type finite
      cases view : type.view <;> simp only [view, View.Finite] at children ⊢
      all_goals first | rfl | exact Bool.or_eq_false_iff.mpr ⟨ihFirst _ children.1, ihLast _ children.2⟩
  | variant tag payload ih =>
      simp only [blockedRaw, finite_root type finite, Bool.false_or]
      have children := finite_view type finite
      cases view : type.view <;> simp only [view, View.Finite] at children ⊢
      all_goals first | rfl | split <;> simp_all

def blocked (pattern : Pattern) (type : Description) : Bool := blockedRaw (pattern.visible false) type

theorem finite_not_blocked (pattern : Pattern) (type : Description) (finite : type.finite = true) :
    blocked pattern type = false := finite_not_blocked_raw _ type finite

theorem variable_capture_allowed (name : Nat) (type : Description) : blocked (.var name) type = false := rfl

theorem constructor_on_clock_rejected : blocked (.variant 7 (.var 0)) .clock = true := rfl

structure Goal where
  role : Nat
  argument : Description
  deriving DecidableEq, Repr

def blockedImpl (implementation : Roles.Impl) (goal : Goal) : Bool :=
  if implementation.role = goal.role then
    match implementation.head with
    | [term] => (decodePattern term).any (fun pattern => blocked pattern goal.argument)
    | _ => false
  else false

def Ready (visible : List Roles.Impl) (goal : Goal) : Prop :=
  goal.argument.recursiveRoot = false ∧ ∀ implementation ∈ visible, blockedImpl implementation goal = false

theorem finite_ready (visible : List Roles.Impl) (goal : Goal) (finite : goal.argument.finite = true) :
    Ready visible goal := by
  refine ⟨finite_root _ finite, ?_⟩
  intro implementation _
  unfold blockedImpl
  split
  · cases head : implementation.head with
    | nil => rfl
    | cons term rest =>
        cases rest with
        | cons _ _ => rfl
        | nil =>
            cases decoded : decodePattern term with
            | none => simp [decoded]
            | some pattern => simp [decoded, finite_not_blocked pattern _ finite]
  · rfl

def instantiate (pattern : Pattern) (assignment : Nat → Description) : Description :=
  match pattern with
  | .var name => assignment name
  | .int => .int
  | .empty => .empty
  | .pair first last => .pair (instantiate first assignment) (instantiate last assignment)
  | .variant tag payload => .variant tag (instantiate payload assignment)
  | .record payload rest => .record (instantiate payload assignment) (instantiate rest assignment)

theorem instantiate_eval (pattern : Pattern) (assignment : Nat → Description) :
    (instantiate pattern assignment).eval = pattern.eval (fun name => (assignment name).eval) := by
  induction pattern <;> simp_all [instantiate, Description.eval, Pattern.eval]

def interpretDescription (term : Roles.Term) (assignment : Nat → Description) : Option Description :=
  (decodePattern term).map (fun pattern => instantiate pattern assignment)

@[simp] theorem interpretDescription_encode (pattern : Pattern) (assignment : Nat → Description) :
    interpretDescription pattern.encode assignment = some (instantiate pattern assignment) := by
  simp [interpretDescription]

def interpretGoal (requirement : Roles.Goal) (assignment : Nat → Description) : Option Goal := do
  let [argument] := requirement.args | none
  return ⟨requirement.role, ← interpretDescription argument assignment⟩

def Matches (implementation : Roles.Impl) (goal : Goal) (assignment : Nat → Common.Ty) : Prop :=
  implementation.role = goal.role ∧
    ∃ term type, implementation.head = [term] ∧ interpretTerm term assignment = some type ∧
      Common.Equivalent type goal.argument.eval

def Unique (visible : List Roles.Impl) (implementation : Roles.Impl) (goal : Goal) : Prop :=
  ∀ other ∈ visible, (∃ assignment : Nat → Common.Ty, Matches other goal assignment) → other = implementation

/-- Independent root outcomes; rejection precedes ambiguity. -/
inductive HeadOutcome (visible : List Roles.Impl) (goal : Goal) where
  | rejected (failure : ¬ Ready visible goal)
  | absent (ready : Ready visible goal) (none : ∀ implementation ∈ visible, ∀ assignment, ¬ Matches implementation goal assignment)
  | ambiguous (ready : Ready visible goal) (first last : Roles.Impl)
      (a : first ∈ visible) (b : last ∈ visible) (different : first ≠ last)
      (matchedFirst : ∃ assignment, Matches first goal assignment)
      (matchedLast : ∃ assignment, Matches last goal assignment)
  | selected (ready : Ready visible goal) (implementation : Roles.Impl) (assignment : Nat → Common.Ty)
      (member : implementation ∈ visible) (matched : Matches implementation goal assignment)
      (unique : Unique visible implementation goal)

mutual
  inductive Dictionary (visible : List Roles.Impl) : Goal → Type where
    | impl {goal} (ready : Ready visible goal) (implementation : Roles.Impl) (assignment : Nat → Description)
        (member : implementation ∈ visible)
        (matched : Matches implementation goal (fun name => (assignment name).eval))
        (unique : Unique visible implementation goal)
        (children : Children visible assignment implementation.constraints) : Dictionary visible goal
  inductive Children (visible : List Roles.Impl) : (Nat → Description) → List Roles.Goal → Type where
    | nil {assignment} : Children visible assignment []
    | cons {assignment} (requirement : Roles.Goal) (child : Goal) (rest : List Roles.Goal)
        (interpreted : interpretGoal requirement assignment = some child)
        (dictionary : Dictionary visible child) (children : Children visible assignment rest) :
        Children visible assignment (requirement :: rest)
end

mutual
  def Dictionary.erase {visible : List Roles.Impl} {goal : Goal} : Dictionary visible goal → RoleDictionaries.Plan
    | .impl _ implementation _ _ _ _ children => .node implementation children.erase
  def Children.erase {visible : List Roles.Impl} {assignment : Nat → Description} {requirements : List Roles.Goal} :
      Children visible assignment requirements → List RoleDictionaries.Plan
    | .nil => []
    | .cons _ _ _ _ dictionary children => dictionary.erase :: children.erase
end

theorem not_ready_no_dictionary (visible : List Roles.Impl) (goal : Goal) (failure : ¬ Ready visible goal) :
    ¬ Nonempty (Dictionary visible goal) := by
  rintro ⟨dictionary⟩
  cases dictionary with
  | impl ready => exact failure ready

theorem Dictionary.all_visible {visible : List Roles.Impl} {goal : Goal} (dictionary : Dictionary visible goal) :
    ∀ implementation ∈ dictionary.erase.declarations, implementation ∈ visible := by
  induction dictionary using Dictionary.rec (motive_2 := fun _ _ children =>
    ∀ implementation ∈ children.erase.flatMap RoleDictionaries.Plan.declarations, implementation ∈ visible) with
  | impl ready implementation assignment member matched unique children ih =>
      intro wanted present
      simp only [Dictionary.erase, RoleDictionaries.Plan.declarations, List.mem_cons] at present
      exact present.elim (fun same => same ▸ member) (ih wanted)
  | nil => contradiction
  | cons requirement child rest interpreted dictionary children ihChild ihRest =>
      rename_i wanted present
      simp only [Children.erase, List.flatMap_cons, List.mem_append] at present
      exact present.elim (ihChild wanted) (ihRest wanted)

end Yulang.CommonRoleInspectedSemantics
