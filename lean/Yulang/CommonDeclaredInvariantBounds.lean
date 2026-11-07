import Yulang.CommonDeclaredNominalSlots
import Yulang.CommonInvariantIntervals

/-!
# Centre-less bounds attached only to declared invariant arguments

An occurrence names a nominal head, an original argument position and two
endpoint references. The actual argument is read from that original head;
it is not chosen or stored as the interval's centre. The finite declaration
lookup must identify this position as invariant. Covariant, contravariant
and unused positions reject this particular interval-attachment operation.

This does not decide where deferred casts are inserted. It attaches already
identified invariant bounds to the existing shared slots, preserving every
repeated occurrence and returning ordinary constraints to the same machine.
-/

namespace Yulang.CommonDeclaredInvariantBounds

open Core.PresenceGeneration (Comp)
open PresenceNormalForm (Atom)
open CommonNominalConstraints (Satisfied append)
open CommonNominalHeads (Argument)
open CommonDeclaredNominalInspection (Kind Parameter Registry DeclaredSubtype argumentKind)
open CommonDeclaredNominalSlots (ArgumentRef HeadRef AllSlots SlotAtom)

structure Occurrence (α : Type) where
  head : HeadRef α
  position : Nat
  lower : ArgumentRef α
  upper : ArgumentRef α

abbrev Selected (α : Type) := Parameter × ArgumentRef α

def Selection (registry : Registry) (occurrence : Occurrence α) (selected : Selected α) : Prop :=
  ∃ declaration, registry[occurrence.head.name]? = some declaration ∧
    declaration[occurrence.position]? = some selected.1 ∧
    occurrence.head.arguments[occurrence.position]? = some selected.2 ∧
    selected.1.variance = .invariant

def select (registry : Registry) (occurrence : Occurrence α) : Option (Selected α) := do
  let declaration ← registry[occurrence.head.name]?
  let parameter ← declaration[occurrence.position]?
  let argument ← occurrence.head.arguments[occurrence.position]?
  if parameter.variance = .invariant then some (parameter, argument) else none

theorem select_exact (registry : Registry) (occurrence : Occurrence α) (selected : Selected α) :
    select registry occurrence = some selected ↔ Selection registry occurrence selected := by
  rcases selected with ⟨parameter, argument⟩
  cases declarationAt : registry[occurrence.head.name]? with
  | none => simp [select, Selection, declarationAt]
  | some declaration =>
      cases parameterAt : declaration[occurrence.position]? with
      | none => simp [select, Selection, declarationAt, parameterAt]
      | some actualParameter =>
          cases argumentAt : occurrence.head.arguments[occurrence.position]? with
          | none => simp [select, Selection, declarationAt, argumentAt]
          | some actualArgument =>
              by_cases invariant : actualParameter.variance = .invariant
              · simp [select, Selection, declarationAt, parameterAt, argumentAt, invariant,
                  Prod.mk.injEq]
                rintro rfl rfl
                exact invariant
              · simp [select, Selection, declarationAt, parameterAt, argumentAt, invariant]
                rintro rfl rfl
                exact invariant

def ArgumentHolds (kind : Kind) (lower actual upper : Argument) : Prop :=
  kind = argumentKind lower ∧ kind = argumentKind actual ∧ kind = argumentKind upper ∧
    lower.Le actual ∧ actual.Le upper

def intervalAtoms (kind : Kind) (lower actual upper : ArgumentRef α) : Option (List (Atom α)) :=
  match kind, lower, actual, upper with
  | .value, (.value, lower), (.value, actual), (.value, upper) =>
      some [.tyLe (.var lower) (.var actual), .tyLe (.var actual) (.var upper)]
  | .row, (.row, lower), (.row, actual), (.row, upper) =>
      some [.rowLe (.var lower) (.var actual), .rowLe (.var actual) (.var upper)]
  | _, _, _, _ => none

theorem interval_atoms_exact (kind : Kind) (lower actual upper : ArgumentRef α)
    (assignment : α → Comp Common.model) :
    Satisfied assignment (intervalAtoms kind lower actual upper) ↔
      ArgumentHolds kind (lower.term.eval assignment) (actual.term.eval assignment)
        (upper.term.eval assignment) := by
  rcases lower with ⟨lowerKind, lower⟩
  rcases actual with ⟨actualKind, actual⟩
  rcases upper with ⟨upperKind, upper⟩
  cases kind <;> cases lowerKind <;> cases actualKind <;> cases upperKind <;>
    simp [intervalAtoms, ArgumentHolds, ArgumentRef.term,
      CommonNominalConstraints.ArgumentTerm.eval, argumentKind, Argument.Le,
      PresenceNormalForm.All, Atom.Holds, Common.model, Core.PresenceGeneration.TyTerm.eval,
      Core.PresenceGeneration.RowTerm.eval]

/-- Ordinary value intervals are exactly the existing centre-less bounds. -/
theorem value_interval_exact (lower actual upper : Common.Ty) :
    ArgumentHolds .value (.value lower) (.value actual) (.value upper) ↔
      CommonInvariantIntervals.Holds (lower, upper) actual := by
  simp [ArgumentHolds, argumentKind, Argument.Le, CommonInvariantIntervals.Holds]

def Holds (registry : Registry) (occurrence : Occurrence α)
    (assignment : α → Comp Common.model) : Prop :=
  ∃ selected, Selection registry occurrence selected ∧
    DeclaredSubtype registry (occurrence.head.term.eval assignment) (occurrence.head.term.eval assignment) ∧
      ArgumentHolds selected.1.kind (occurrence.lower.term.eval assignment)
        (selected.2.term.eval assignment) (occurrence.upper.term.eval assignment)

def inspect (registry : Registry) (occurrence : Occurrence α) : Option (List (Atom α)) :=
  match select registry occurrence with
  | none => none
  | some (parameter, actual) =>
      append (CommonDeclaredNominalSlots.inspect registry (occurrence.head, occurrence.head))
        (intervalAtoms parameter.kind occurrence.lower actual occurrence.upper)

theorem inspect_exact (registry : Registry) (occurrence : Occurrence α)
    (assignment : α → Comp Common.model) :
    Satisfied assignment (inspect registry occurrence) ↔ Holds registry occurrence assignment := by
  simp only [Holds, ← select_exact]
  cases selectEq : select registry occurrence with
  | none => simp [inspect, selectEq]
  | some selected =>
      cases selected with
      | mk parameter actual =>
          simp [inspect, selectEq, CommonNominalConstraints.append_exact,
            CommonDeclaredNominalSlots.inspect, CommonDeclaredNominalInspection.inspect_exact,
            interval_atoms_exact]

def inspectAll (registry : Registry) : List (Occurrence α) → Option (List (Atom α))
  | [] => some []
  | occurrence :: rest => append (inspect registry occurrence) (inspectAll registry rest)

def Models (registry : Registry) (occurrences : List (Occurrence α))
    (assignment : α → Comp Common.model) : Prop :=
  ∀ occurrence ∈ occurrences, Holds registry occurrence assignment

theorem inspect_all_exact (registry : Registry) (occurrences : List (Occurrence α))
    (assignment : α → Comp Common.model) :
    Satisfied assignment (inspectAll registry occurrences) ↔ Models registry occurrences assignment := by
  induction occurrences with
  | nil => simp [inspectAll, Models, PresenceNormalForm.All]
  | cons occurrence rest ih =>
      simp only [inspectAll, CommonNominalConstraints.append_exact, inspect_exact, ih,
        Models, List.mem_cons, forall_eq_or_imp]

private theorem interval_atoms_slots (kind : Kind) (lower actual upper : ArgumentRef α)
    (atoms : List (Atom α)) (returned : intervalAtoms kind lower actual upper = some atoms) : AllSlots atoms := by
  rcases lower with ⟨lowerKind, lower⟩
  rcases actual with ⟨actualKind, actual⟩
  rcases upper with ⟨upperKind, upper⟩
  cases kind <;> cases lowerKind <;> cases actualKind <;> cases upperKind <;>
    simp [intervalAtoms] at returned
  all_goals subst atoms
  all_goals simp [AllSlots, SlotAtom.value, SlotAtom.row]

private theorem append_slots (first last : Option (List (Atom α)))
    (left : ∀ atoms, first = some atoms → AllSlots atoms)
    (right : ∀ atoms, last = some atoms → AllSlots atoms)
    (atoms : List (Atom α)) (returned : append first last = some atoms) : AllSlots atoms := by
  cases first with
  | none => simp [append] at returned
  | some first =>
      cases last with
      | none => simp [append] at returned
      | some last =>
          have returned : first ++ last = atoms := Option.some.inj returned
          subst atoms
          exact (left first rfl).append (right last rfl)

theorem inspect_slots (registry : Registry) (occurrence : Occurrence α)
    (atoms : List (Atom α)) (returned : inspect registry occurrence = some atoms) : AllSlots atoms := by
  unfold inspect at returned
  cases selectEq : select registry occurrence with
  | none => simp [selectEq] at returned
  | some selected =>
      cases selected with
      | mk parameter actual =>
          simp only [selectEq] at returned
          apply append_slots _ _ ?_ (interval_atoms_slots parameter.kind occurrence.lower actual occurrence.upper) atoms returned
          intro selfAtoms selfReturned
          apply CommonDeclaredNominalSlots.inspect_all_slots registry [(occurrence.head, occurrence.head)] selfAtoms
          simp [CommonDeclaredNominalSlots.inspectAll, selfReturned, append]

theorem inspect_all_slots (registry : Registry) (occurrences : List (Occurrence α))
    (atoms : List (Atom α)) (returned : inspectAll registry occurrences = some atoms) : AllSlots atoms := by
  induction occurrences generalizing atoms with
  | nil => simp [inspectAll] at returned; subst atoms; simp [AllSlots]
  | cons occurrence rest ih =>
      exact append_slots _ _ (inspect_slots registry occurrence) ih atoms returned

end Yulang.CommonDeclaredInvariantBounds
