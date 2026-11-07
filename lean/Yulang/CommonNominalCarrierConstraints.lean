import Yulang.CommonNominalModel
import Yulang.PresenceNormalForm

/-!
# Finite invariant comparisons over the full nested nominal carrier

Both directions are emitted as actual presence atoms. The same assignment is
used at all argument occurrences, including value/row sharing. The arguments
range over the new carrier itself, not the old head-only Common argument type.
This is comparison generation; solving every generated source construction is
not inferred from this theorem.
-/

namespace Yulang.CommonNominalCarrierConstraints

open Core.PresenceGeneration (Comp TyTerm RowTerm)
open PresenceNormalForm (Atom All)
open CommonNominalCarrier

inductive ArgumentTerm (α : Type) where
  | value : TyTerm α → ArgumentTerm α
  | row : RowTerm α → ArgumentTerm α

def ArgumentTerm.eval (assignment : α → Comp model) : ArgumentTerm α → Argument
  | .value type => .inl (type.eval model assignment)
  | .row effect => .inr (effect.eval model assignment)

structure HeadTerm (α : Type) where
  name : Nat
  arguments : List (ArgumentTerm α)

def HeadTerm.eval (assignment : α → Comp model) (head : HeadTerm α) : Ty :=
  nominal head.name (head.arguments.map (ArgumentTerm.eval assignment))

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

def Satisfied (assignment : α → Comp model) (result : Option (List (Atom α))) : Prop :=
  ∃ atoms, result = some atoms ∧ All model assignment atoms

@[simp] theorem satisfied_none (assignment : α → Comp model) :
    ¬ Satisfied assignment none := by simp [Satisfied]

@[simp] theorem satisfied_some (assignment : α → Comp model) (atoms : List (Atom α)) :
    Satisfied assignment (some atoms) ↔ All model assignment atoms := by simp [Satisfied]

theorem append_exact (assignment : α → Comp model)
    (first last : Option (List (Atom α))) :
    Satisfied assignment (append first last) ↔
      Satisfied assignment first ∧ Satisfied assignment last := by
  cases first <;> cases last <;> simp [append, PresenceNormalForm.all_append]

theorem compileArgument_exact (assignment : α → Comp model)
    (first last : ArgumentTerm α) :
    Satisfied assignment (compileArgument first last) ↔
      ArgumentEquivalent (first.eval assignment) (last.eval assignment) := by
  cases first <;> cases last <;>
    simp [compileArgument, ArgumentTerm.eval, ArgumentEquivalent,
      Equivalent, All, Atom.Holds, model]
  constructor
  · rintro ⟨forward, backward⟩
    exact Common.rowLe_antisymm forward backward
  · intro same
    rw [same]
    exact ⟨Common.rowLe_refl _, Common.rowLe_refl _⟩

private def Aligned : List Argument → List Argument → Prop
  | [], [] => True
  | first :: rest, last :: tail => ArgumentEquivalent first last ∧ Aligned rest tail
  | _, _ => False

private theorem aligned_exact (first last : List Argument) :
    Aligned first last ↔ first.length = last.length ∧ ArgumentsEquivalent first last := by
  induction first generalizing last with
  | nil => cases last <;> simp [Aligned, ArgumentsEquivalent]
  | cons head tail ih =>
      cases last with
      | nil => simp [Aligned]
      | cons head' tail' =>
          simp only [Aligned, ih, List.length_cons, Nat.add_right_cancel_iff]
          constructor
          · rintro ⟨same, size, rest⟩
            refine ⟨size, ?_⟩
            intro index a b left right
            cases index with
            | zero =>
                simp only [List.getElem?_cons_zero, Option.some.injEq] at left right
                subst a; subst b
                exact same
            | succ index => exact rest index a b left right
          · rintro ⟨size, same⟩
            exact ⟨same 0 head head' rfl rfl, size,
              fun index a b left right => same (index + 1) a b left right⟩

theorem compileArguments_exact (assignment : α → Comp model)
    (first last : List (ArgumentTerm α)) :
    Satisfied assignment (compileArguments first last) ↔
      (first.length = last.length ∧
        ArgumentsEquivalent (first.map (ArgumentTerm.eval assignment))
          (last.map (ArgumentTerm.eval assignment))) := by
  have recursive : Satisfied assignment (compileArguments first last) ↔
      Aligned (first.map (ArgumentTerm.eval assignment))
        (last.map (ArgumentTerm.eval assignment)) := by
    induction first generalizing last with
    | nil => cases last <;> simp [compileArguments, Aligned]
    | cons head tail ih =>
        cases last with
        | nil => simp [compileArguments, Aligned]
        | cons head' tail' =>
            simp only [compileArguments, append_exact, compileArgument_exact, ih,
              List.map_cons, Aligned]
  simpa only [List.length_map] using recursive.trans (aligned_exact _ _)

/-- Arbitrary shared slot type, arbitrary nominal descriptions and arbitrary
assignments of full nested/regular nominal values and arbitrary rows. All
comparison directions are finite generated atoms, not an external oracle. -/
theorem compile_nominal_comparison_exact (first last : HeadTerm α)
    (assignment : α → Comp model) :
    (∃ atoms, compile first last = some atoms ∧ All model assignment atoms) ↔
      CommonNominalCarrier.Subtype (first.eval assignment) (last.eval assignment) := by
  change Satisfied assignment (compile first last) ↔ _
  simp only [HeadTerm.eval, nominal_regular_invariant_exact, List.length_map]
  by_cases identity : first.name = last.name
  · simp only [compile, identity, ↓reduceIte, compileArguments_exact, true_and]
  · simp [compile, identity]

end Yulang.CommonNominalCarrierConstraints
