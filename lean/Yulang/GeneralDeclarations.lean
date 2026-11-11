import Yulang.GeneralDeclarationPatterns
import Yulang.GeneralSourceState

/-!
# General declarations, output-only binders, and independent checking

One clause retains its role, every unnamed argument, and every named output
equation. Identities are source identities, not positions in a reordered list.
The owner decision of 2026-11-12 makes generated associated binders output-only.
Only unnamed child arguments participate in the two Paterson comparisons.

Checked is a declaration-only certificate judgment. In particular its universal
capture-stability field is not replaced by a fragment's finite checker.
Residual normalization coverage is explicit and can defer certification.
-/
namespace Yulang.GeneralDeclarations

open GeneralDeclarationPatterns

structure Equation where
  id : Nat
  name : Nat
  rhs : Pattern
  deriving Repr, DecidableEq

structure Clause where
  id : Nat
  role : Nat
  arguments : List Pattern
  outputs : List Equation
  deriving Repr, DecidableEq

/-- The producing clause and equation are retained even if the binder is used
in several other named equations. No input occurrence is licensed by this. -/
structure OutputBinder where
  name : Nat
  clause : Nat
  equation : Nat
  deriving Repr, DecidableEq

structure Declaration where
  id : Nat
  role : Nat
  head : List Pattern
  requirements : List Clause
  associated : List Equation
  outputBinders : List OutputBinder
  deriving Repr, DecidableEq

def Declaration.inputNames (declaration : Declaration) : List Nat :=
  variablesArgs (normalizeArgs declaration.head)

def Declaration.outputNames (declaration : Declaration) : List Nat :=
  declaration.outputBinders.map OutputBinder.name

/-- The normalized head exposed to the candidate layer; the original spelling
is also retained for provenance and lexical output-only checks. -/
def Declaration.normalHead (declaration : Declaration) : List Pattern :=
  normalizeArgs declaration.head

def NormalizationDeferred (declaration : Declaration) : Prop :=
  ∃ clause ∈ declaration.requirements,
    ¬ CountsCovered declaration.head clause.arguments ∨
      ¬ ConservativeSmaller declaration.head clause.arguments

def Declared (roles : Roles.RoleDecls) (role : Nat) (equation : Equation) : Prop :=
  ∃ body, (roles role).assoc equation.name = some body

def Clause.Signature (roles : Roles.RoleDecls) (clause : Clause) : Prop :=
  clause.arguments.length = (roles clause.role).arity ∧
    ∀ equation ∈ clause.outputs, Declared roles clause.role equation

def Declaration.Signature (roles : Roles.RoleDecls) (declaration : Declaration) : Prop :=
  declaration.head.length = (roles declaration.role).arity ∧
    (∀ equation ∈ declaration.associated, Declared roles declaration.role equation) ∧
    (∀ name body, (roles declaration.role).assoc name = some body →
      (∃ equation ∈ declaration.associated, equation.name = name) ∨ body.isSome = true) ∧
    ∀ clause ∈ declaration.requirements, clause.Signature roles

def Declaration.Identified (declaration : Declaration) : Prop :=
  (declaration.requirements.map Clause.id).Nodup ∧
    (declaration.associated.map Equation.id).Nodup ∧
    (declaration.associated.map Equation.name).Nodup ∧
    declaration.outputNames.Nodup ∧
    ∀ clause ∈ declaration.requirements, (clause.outputs.map Equation.id).Nodup

def Declaration.Produced (declaration : Declaration) : Prop :=
  ∀ binder ∈ declaration.outputBinders,
    ∃ clause ∈ declaration.requirements, clause.id = binder.clause ∧
      ∃ equation ∈ clause.outputs, equation.id = binder.equation ∧ equation.rhs = .var binder.name

/-- A lexical output-only restriction, in addition to normalized counting.
It cannot be bypassed by hiding an input occurrence in an erased field. -/
def Declaration.OutputOnly (declaration : Declaration) : Prop :=
  (∀ name ∈ declaration.outputNames, name ∉ variablesArgs declaration.head) ∧
    ∀ clause ∈ declaration.requirements, ∀ name ∈ declaration.outputNames,
      name ∉ variablesArgs clause.arguments

def Declaration.Scoped (declaration : Declaration) : Prop :=
  (∀ clause ∈ declaration.requirements,
    ∀ name ∈ variablesArgs (normalizeArgs clause.arguments), name ∈ declaration.inputNames) ∧
  (∀ equation ∈ declaration.associated, ∀ name ∈ (normalize equation.rhs).variables,
    name ∈ declaration.inputNames ∨ name ∈ declaration.outputNames) ∧
  (∀ clause ∈ declaration.requirements, ∀ equation ∈ clause.outputs,
    ∀ name ∈ equation.rhs.variables,
      name ∈ declaration.inputNames ∨ name ∈ declaration.outputNames)

def Declaration.ConstructorScoped (constructors : Constructors) (declaration : Declaration) : Prop :=
  ArgsWellScoped constructors declaration.head ∧
    (∀ clause ∈ declaration.requirements, ArgsWellScoped constructors clause.arguments ∧
      ∀ equation ∈ clause.outputs, WellScoped constructors equation.rhs) ∧
    ∀ equation ∈ declaration.associated, WellScoped constructors equation.rhs

/-- A general certificate contract over the declared finite patterns. The
coverage and conservative bounds are sufficient checks; their failure alone
must not be reported as a language rejection. -/
structure DeclarationChecked (constructors : Constructors) (roles : Roles.RoleDecls)
    (declaration : Declaration) : Prop where
  signature : declaration.Signature roles
  identified : declaration.Identified
  produced : declaration.Produced
  outputOnly : declaration.OutputOnly
  scope : declaration.Scoped
  constructorScoped : declaration.ConstructorScoped constructors
  countsCovered : ∀ clause ∈ declaration.requirements, CountsCovered declaration.head clause.arguments
  paterson : ∀ clause ∈ declaration.requirements, Smaller declaration.head clause.arguments
  conservative : ∀ clause ∈ declaration.requirements, ConservativeSmaller declaration.head clause.arguments
  captureStable : ∀ clause ∈ declaration.requirements, StableSmaller declaration.head clause.arguments

structure Registry where
  constructors : Constructors
  roles : Roles.RoleDecls
  declarations : List Declaration

def Checked (registry : Registry) : Prop :=
  (registry.declarations.map Declaration.id).Nodup ∧
    ∀ declaration ∈ registry.declarations,
      DeclarationChecked registry.constructors registry.roles declaration

abbrev CheckedRegistry := { registry : Registry // Checked registry }

theorem deferred_not_certified (declaration : Declaration) (deferred : NormalizationDeferred declaration) :
    ¬ DeclarationChecked constructors roles declaration := by
  rintro checked
  obtain ⟨clause, present, uncovered | unbounded⟩ := deferred
  · exact uncovered (checked.countsCovered clause present)
  · exact unbounded (checked.conservative clause present)

theorem checked_child_descent (checked : DeclarationChecked constructors roles declaration)
    (clause : Clause) (present : clause ∈ declaration.requirements) (capture : Nat → Pattern) :
    Smaller (substArgs capture declaration.head) (substArgs capture clause.arguments) :=
  checked.captureStable clause present capture

theorem output_input_rejected (declaration : Declaration) (clause : Clause)
    (present : clause ∈ declaration.requirements) (name : Nat)
    (output : name ∈ declaration.outputNames) (input : name ∈ variablesArgs clause.arguments) :
    ¬ DeclarationChecked constructors roles declaration :=
  fun checked => checked.outputOnly.2 clause present name output input

theorem late_merge_rejected (declaration : Declaration) (clause : Clause)
    (present : clause ∈ declaration.requirements) (capture : Nat → Pattern)
    (noDecrease : ¬ Roles.argsSize (counted (substArgs capture clause.arguments)) <
      Roles.argsSize (counted (substArgs capture declaration.head))) :
    ¬ DeclarationChecked constructors roles declaration :=
  fun checked => noDecrease (checked.captureStable clause present capture).1

/-- A fixed local interpretation of the named output constraints. No resolver
is called. A later dictionary semantics must supply this functionality. -/
abbrev Associated := Nat → List Pattern → Nat → Pattern

def SatisfiesOutputs (associated : Associated) (declaration : Declaration) (capture : Nat → Pattern) : Prop :=
  ∀ clause ∈ declaration.requirements, ∀ equation ∈ clause.outputs,
    equation.rhs.subst capture =
      associated clause.role (substArgs capture (normalizeArgs clause.arguments)) equation.name

/-- Head agreement is agreement of the actual captured bindings, not arbitrary
solutions of a head-equivalence equation. The source matcher bridge is separate. -/
def CapturesAgree (declaration : Declaration) (first last : Nat → Pattern) : Prop :=
  ∀ name ∈ declaration.inputNames, first name = last name

theorem outputs_determined (checked : DeclarationChecked constructors roles declaration)
    (associated : Associated) (first last : Nat → Pattern)
    (head : CapturesAgree declaration first last)
    (firstOutputs : SatisfiesOutputs associated declaration first)
    (lastOutputs : SatisfiesOutputs associated declaration last) :
    ∀ name ∈ declaration.outputNames, first name = last name := by
  intro name member
  obtain ⟨binder, present, same⟩ := List.mem_map.mp member
  obtain ⟨clause, child, _, equation, output, _, producer⟩ := checked.produced binder present
  have inputs := substArgs_congr (normalizeArgs clause.arguments) first last
    (fun name occurs => head name (checked.scope.1 clause child name occurs))
  have left := firstOutputs clause child equation output
  have right := lastOutputs clause child equation output
  rw [producer, Pattern.subst] at left right
  rw [inputs] at left
  simpa only [← same] using left.trans right.symm

theorem capture_determines_associated (checked : DeclarationChecked constructors roles declaration)
    (associated : Associated) (first last : Nat → Pattern)
    (head : CapturesAgree declaration first last)
    (firstOutputs : SatisfiesOutputs associated declaration first)
    (lastOutputs : SatisfiesOutputs associated declaration last)
    (equation : Equation) (present : equation ∈ declaration.associated) :
    (normalize equation.rhs).subst first = (normalize equation.rhs).subst last := by
  apply subst_congr
  intro name member
  rcases checked.scope.2.1 equation present name member with input | output
  · exact head name input
  · exact outputs_determined checked associated first last head firstOutputs lastOutputs name output

end Yulang.GeneralDeclarations
