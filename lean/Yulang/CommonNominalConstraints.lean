import Yulang.CommonNominalHeads
import Yulang.PresenceNormalForm

/-!
# Finite constraints for invariant nominal heads

The compiler retains each symbolic argument and emits both comparison
directions. It uses the existing finite presence atoms, not a nominal
subtyping oracle or a semantic predicate embedded in a formula. All argument
terms are evaluated by the actual common type/row interpreter, so repeated
slot IDs keep their sharing and arbitrary common assignments are permitted.

This is the nominal comparison component of a source generator. It does not
yet add nominal nodes to the shared regular graph or solve constructor-site
constraints. A returned atom list can still be inconsistent.
-/

namespace Yulang.CommonNominalConstraints

open Core.PresenceGeneration (Comp TyTerm RowTerm)
open PresenceNormalForm (Atom All)
open CommonNominalHeads (Argument Head ArgumentsEquivalent)

inductive ArgumentTerm (α : Type) where
  | value : TyTerm α → ArgumentTerm α
  | row : RowTerm α → ArgumentTerm α

def ArgumentTerm.eval (assignment : α → Comp Common.model) : ArgumentTerm α → Argument
  | .value type => .value (type.eval Common.model assignment)
  | .row effect => .row (effect.eval Common.model assignment)

structure HeadTerm (α : Type) where
  name : Nat
  arguments : List (ArgumentTerm α)

def HeadTerm.eval (assignment : α → Comp Common.model) (head : HeadTerm α) : Head :=
  ⟨head.name, head.arguments.map (ArgumentTerm.eval assignment)⟩

def compileArgument : ArgumentTerm α → ArgumentTerm α → Option (List (Atom α))
  | .value first, .value last => some [.tyLe first last, .tyLe last first]
  | .row first, .row last => some [.rowLe first last, .rowLe last first]
  | _, _ => none

def append (first last : Option (List (Atom α))) : Option (List (Atom α)) := do
  let left ← first
  let right ← last
  return left ++ right

def compileArguments : List (ArgumentTerm α) → List (ArgumentTerm α) → Option (List (Atom α))
  | [], [] => some []
  | first :: rest, last :: tail => append (compileArgument first last) (compileArguments rest tail)
  | _, _ => none

def compile (first last : HeadTerm α) : Option (List (Atom α)) :=
  if first.name = last.name then compileArguments first.arguments last.arguments else none

def Satisfied (assignment : α → Comp Common.model) (result : Option (List (Atom α))) : Prop :=
  ∃ atoms, result = some atoms ∧ All Common.model assignment atoms

@[simp] theorem satisfied_none (assignment : α → Comp Common.model) :
    ¬ Satisfied assignment none := by simp [Satisfied]

@[simp] theorem satisfied_some (assignment : α → Comp Common.model) (atoms : List (Atom α)) :
    Satisfied assignment (some atoms) ↔ All Common.model assignment atoms := by simp [Satisfied]

theorem append_exact (assignment : α → Comp Common.model)
    (first last : Option (List (Atom α))) :
    Satisfied assignment (append first last) ↔
      Satisfied assignment first ∧ Satisfied assignment last := by
  cases first <;> cases last <;> simp [append, PresenceNormalForm.all_append]

theorem compileArgument_exact (assignment : α → Comp Common.model)
    (first last : ArgumentTerm α) :
    Satisfied assignment (compileArgument first last) ↔
      (first.eval assignment).Equivalent (last.eval assignment) := by
  cases first <;> cases last <;>
    simp [compileArgument, ArgumentTerm.eval, Argument.Equivalent, Argument.Le,
      All, Atom.Holds, Common.model]

theorem compileArguments_exact (assignment : α → Comp Common.model)
    (first last : List (ArgumentTerm α)) :
    Satisfied assignment (compileArguments first last) ↔
      ArgumentsEquivalent (first.map (ArgumentTerm.eval assignment))
        (last.map (ArgumentTerm.eval assignment)) := by
  induction first generalizing last with
  | nil => cases last <;> simp [compileArguments, ArgumentsEquivalent]
  | cons head rest ih =>
      cases last with
      | nil => simp [compileArguments, ArgumentsEquivalent]
      | cons last tail =>
          simp only [compileArguments, append_exact, compileArgument_exact, ih,
            List.map_cons, ArgumentsEquivalent]

/-- Every finite pair of nominal head descriptions and every independent
common computation assignment, with no success or consistency premise. -/
theorem compile_nominal_comparison_exact (first last : HeadTerm α)
    (assignment : α → Comp Common.model) :
    (∃ atoms, compile first last = some atoms ∧ All Common.model assignment atoms) ↔
      CommonNominalHeads.Subtype (first.eval assignment) (last.eval assignment) := by
  change Satisfied assignment (compile first last) ↔ _
  rw [CommonNominalHeads.nominal_head_invariant_exact]
  by_cases identity : first.name = last.name
  · simp only [compile, identity, ↓reduceIte, compileArguments_exact, HeadTerm.eval,
      List.length_map, true_and]
    constructor
    · intro same
      exact ⟨by simpa only [List.length_map] using
        (CommonNominalHeads.argumentsEquivalent_iff _ _).mp same |>.1, same⟩
    · exact fun pair => pair.2
  · simp [compile, identity, HeadTerm.eval]

end Yulang.CommonNominalConstraints
