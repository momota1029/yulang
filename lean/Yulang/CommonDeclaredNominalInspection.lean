import Yulang.CommonDeclaredNominalVariance
import Yulang.CommonNominalConstraints

/-!
# Finite declaration-directed nominal inspection

The declaration table is indexed by nominal identity and fixes the ordered
kind and variance of every argument before expression inference. The actual
inspector validates lookup, arity and both argument kinds, including unused
positions, then emits ordinary type/row inequalities over the ORIGINAL terms.

Arguments denote actual instances. Open invariant bounds constrain their
original shared slots separately; this compiler does not choose an interval
centre or perform source construction. Deriving variance from recursive
source declarations and extending the full recursive nominal carrier remain
separate obligations.
-/

namespace Yulang.CommonDeclaredNominalInspection

open Core.PresenceGeneration (Comp)
open PresenceNormalForm (Atom All)
open CommonNominalHeads (Argument Head)
open CommonNominalConstraints (ArgumentTerm HeadTerm Satisfied append)
open CommonDeclaredNominalVariance (Variance modeAt)

inductive Kind where
  | value
  | row
  deriving DecidableEq, Repr

structure Parameter where
  kind : Kind
  variance : Variance
  deriving DecidableEq, Repr

abbrev Declaration := List Parameter
abbrev Registry := List Declaration

def argumentKind : Argument → Kind
  | .value _ => .value
  | .row _ => .row

def termKind : ArgumentTerm α → Kind
  | .value _ => .value
  | .row _ => .row

@[simp] theorem argument_kind_eval (assignment : α → Comp Common.model)
    (term : ArgumentTerm α) : argumentKind (term.eval assignment) = termKind term := by
  cases term <;> rfl

def WellKinded : Declaration → List Argument → Prop
  | [], [] => True
  | parameter :: rest, argument :: tail =>
      parameter.kind = argumentKind argument ∧ WellKinded rest tail
  | _, _ => False

def ArgumentRel (parameter : Parameter) (first last : Argument) : Prop :=
  parameter.kind = argumentKind first ∧ parameter.kind = argumentKind last ∧
    parameter.variance.Rel first last

def ArgumentsRel : Declaration → List Argument → List Argument → Prop
  | [], [], [] => True
  | parameter :: rest, first :: tail, last :: suffix =>
      ArgumentRel parameter first last ∧ ArgumentsRel rest tail suffix
  | _, _, _ => False

theorem wellKinded_length (declaration : Declaration) (arguments : List Argument)
    (kinded : WellKinded declaration arguments) : declaration.length = arguments.length := by
  induction declaration generalizing arguments with
  | nil => cases arguments <;> simp_all [WellKinded]
  | cons parameter rest ih =>
      cases arguments with
      | nil => cases kinded
      | cons argument tail => exact congrArg Nat.succ (ih tail kinded.2)

theorem arguments_relation_exact (declaration : Declaration) (first last : List Argument) :
    ArgumentsRel declaration first last ↔
      WellKinded declaration first ∧ WellKinded declaration last ∧
        ∀ (index : Nat) (a b : Argument),
          first[index]? = some a → last[index]? = some b →
            (modeAt (declaration.map Parameter.variance) index).Rel a b := by
  induction declaration generalizing first last with
  | nil => cases first <;> cases last <;> simp [ArgumentsRel, WellKinded]
  | cons parameter rest ih =>
      cases first with
      | nil => cases last <;> simp [ArgumentsRel, WellKinded]
      | cons first tail =>
          cases last with
          | nil => simp [ArgumentsRel, WellKinded]
          | cons last suffix =>
              constructor
              · rintro ⟨⟨firstKind, lastKind, related⟩, tailRelated⟩
                obtain ⟨firstTail, lastTail, tailPointwise⟩ := (ih tail suffix).mp tailRelated
                refine ⟨⟨firstKind, firstTail⟩, ⟨lastKind, lastTail⟩, ?_⟩
                intro index a b firstAt lastAt
                cases index with
                | zero =>
                    simp only [List.getElem?_cons_zero, Option.some.injEq] at firstAt lastAt
                    subst a; subst b
                    exact related
                | succ index => exact tailPointwise index a b firstAt lastAt
              · rintro ⟨⟨firstKind, firstTail⟩, ⟨lastKind, lastTail⟩, pointwise⟩
                refine ⟨⟨firstKind, lastKind, pointwise 0 first last rfl rfl⟩,
                  (ih tail suffix).mpr ⟨firstTail, lastTail, ?_⟩⟩
                intro index a b firstAt lastAt
                exact pointwise (index + 1) a b firstAt lastAt

/-- The independent judgment uses the already proved nominal demand order,
with explicit declaration-kind and arity validation. No missing variance
entry can be read as an unchecked unused position. -/
theorem arguments_demand_exact (declaration : Declaration) (first last : Head) :
    (WellKinded declaration first.arguments ∧ WellKinded declaration last.arguments ∧
      CommonDeclaredNominalVariance.Subtype (declaration.map Parameter.variance) first last) ↔
    first.name = last.name ∧ ArgumentsRel declaration first.arguments last.arguments := by
  rw [CommonDeclaredNominalVariance.nominal_head_variance_exact, arguments_relation_exact]
  constructor
  · rintro ⟨firstKind, lastKind, same, _, related⟩
    exact ⟨same, firstKind, lastKind, related⟩
  · rintro ⟨same, firstKind, lastKind, related⟩
    exact ⟨firstKind, lastKind, same,
      (wellKinded_length declaration first.arguments firstKind).symm.trans
        (wellKinded_length declaration last.arguments lastKind), related⟩

def directions (mode : Variance) (forward backward : Atom α) : List (Atom α) :=
  match mode with
  | .covariant => [forward]
  | .contravariant => [backward]
  | .invariant => [forward, backward]
  | .unused => []

def inspectArgument (parameter : Parameter) (first last : ArgumentTerm α) :
    Option (List (Atom α)) :=
  if parameter.kind = termKind first ∧ parameter.kind = termKind last then
    match first, last with
    | .value a, .value b => some (directions parameter.variance (.tyLe a b) (.tyLe b a))
    | .row a, .row b => some (directions parameter.variance (.rowLe a b) (.rowLe b a))
    | _, _ => none
  else none

theorem inspect_argument_exact (assignment : α → Comp Common.model) (parameter : Parameter)
    (first last : ArgumentTerm α) :
    Satisfied assignment (inspectArgument parameter first last) ↔
      ArgumentRel parameter (first.eval assignment) (last.eval assignment) := by
  rcases parameter with ⟨kind, mode⟩
  cases kind <;> cases mode <;> cases first <;> cases last <;>
    simp [inspectArgument, termKind, directions, ArgumentRel, argumentKind, ArgumentTerm.eval,
      Variance.Rel, Argument.Equivalent, Argument.Le, All, Atom.Holds, Common.model]

def inspectArguments : Declaration → List (ArgumentTerm α) → List (ArgumentTerm α) →
    Option (List (Atom α))
  | [], [], [] => some []
  | parameter :: rest, first :: tail, last :: suffix =>
      append (inspectArgument parameter first last) (inspectArguments rest tail suffix)
  | _, _, _ => none

theorem inspect_arguments_exact (assignment : α → Comp Common.model) (declaration : Declaration)
    (first last : List (ArgumentTerm α)) :
    Satisfied assignment (inspectArguments declaration first last) ↔
      ArgumentsRel declaration (first.map (ArgumentTerm.eval assignment))
        (last.map (ArgumentTerm.eval assignment)) := by
  induction declaration generalizing first last with
  | nil => cases first <;> cases last <;> simp [inspectArguments, ArgumentsRel, All]
  | cons parameter rest ih =>
      cases first with
      | nil => cases last <;> simp [inspectArguments, ArgumentsRel]
      | cons first tail =>
          cases last with
          | nil => simp [inspectArguments, ArgumentsRel]
          | cons last suffix =>
              simp only [inspectArguments, CommonNominalConstraints.append_exact,
                inspect_argument_exact, ih, List.map_cons, ArgumentsRel]

def DeclaredSubtype (registry : Registry) (first last : Head) : Prop :=
  ∃ declaration, registry[first.name]? = some declaration ∧
    WellKinded declaration first.arguments ∧ WellKinded declaration last.arguments ∧
      CommonDeclaredNominalVariance.Subtype (declaration.map Parameter.variance) first last

theorem declared_subtype_exact (registry : Registry) (first last : Head) :
    DeclaredSubtype registry first last ↔
      ∃ declaration, registry[first.name]? = some declaration ∧
        first.name = last.name ∧ ArgumentsRel declaration first.arguments last.arguments :=
  exists_congr fun declaration =>
    and_congr Iff.rfl (arguments_demand_exact declaration first last)

def inspect (registry : Registry) (first last : HeadTerm α) : Option (List (Atom α)) :=
  if first.name = last.name then
    match registry[first.name]? with
    | none => none
    | some declaration => inspectArguments declaration first.arguments last.arguments
  else none

/-- Every finite declaration table, every ordered pair of original type/row
argument terms, and every independent assignment. Lookup/ID/arity/kind errors
are rejected by the actual inspector; constraints retain all original terms. -/
theorem inspect_exact (registry : Registry) (first last : HeadTerm α)
    (assignment : α → Comp Common.model) :
    Satisfied assignment (inspect registry first last) ↔
      DeclaredSubtype registry (first.eval assignment) (last.eval assignment) := by
  rw [declared_subtype_exact]
  unfold inspect
  split
  · rename_i same
    cases found : registry[first.name]? with
    | none => simp [HeadTerm.eval, found]
    | some declaration =>
        simp only [inspect_arguments_exact]
        constructor
        · intro related
          exact ⟨declaration, found, same, related⟩
        · rintro ⟨other, selected, _, related⟩
          have equal : declaration = other := Option.some.inj (found.symm.trans selected)
          subst other
          exact related
  · rename_i different
    constructor
    · intro impossible
      exact (CommonNominalConstraints.satisfied_none assignment impossible).elim
    · rintro ⟨_, _, same, _⟩
      exact (different same).elim

end Yulang.CommonDeclaredNominalInspection
