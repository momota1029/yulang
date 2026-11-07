import Yulang.CommonDeclaredNominalInspection
import Yulang.PresenceGeneratedWidth
import Yulang.PresenceSourceConstraintSupport

/-!
# Declared nominal constraints on original shared slots

This is the actual declaration-directed inspector, specialized by supplying
original value/row variable references as its arguments. Every emitted atom
belongs internally to the existing Common worklist grammar. No new solver,
semantic carrier, compatibility oracle or argument allocator is introduced.
-/

namespace Yulang.CommonDeclaredNominalSlots

open Core.PresenceGeneration (Comp)
open PresenceNormalForm (Atom)
open CommonNominalConstraints (ArgumentTerm HeadTerm Satisfied append)
open CommonDeclaredNominalInspection (Kind Parameter Declaration Registry DeclaredSubtype)

abbrev ArgumentRef (α : Type) := Kind × α

def ArgumentRef.term (argument : ArgumentRef α) : ArgumentTerm α :=
  match argument.1 with
  | .value => .value (.var argument.2)
  | .row => .row (.var argument.2)

structure HeadRef (α : Type) where
  name : Nat
  arguments : List (ArgumentRef α)

def HeadRef.term (head : HeadRef α) : HeadTerm α :=
  ⟨head.name, head.arguments.map ArgumentRef.term⟩

abbrev Comparison (α : Type) := HeadRef α × HeadRef α

def inspect (registry : Registry) (comparison : Comparison α) : Option (List (Atom α)) :=
  CommonDeclaredNominalInspection.inspect registry comparison.1.term comparison.2.term

def inspectAll (registry : Registry) : List (Comparison α) → Option (List (Atom α))
  | [] => some []
  | comparison :: rest => append (inspect registry comparison) (inspectAll registry rest)

def Models (registry : Registry) (comparisons : List (Comparison α))
    (assignment : α → Comp Common.model) : Prop :=
  ∀ comparison ∈ comparisons,
    DeclaredSubtype registry (comparison.1.term.eval assignment) (comparison.2.term.eval assignment)

theorem inspect_all_exact (registry : Registry) (comparisons : List (Comparison α))
    (assignment : α → Comp Common.model) :
    Satisfied assignment (inspectAll registry comparisons) ↔ Models registry comparisons assignment := by
  induction comparisons with
  | nil => simp [inspectAll, Models, PresenceNormalForm.All]
  | cons comparison rest ih =>
      simp only [inspectAll, CommonNominalConstraints.append_exact, inspect,
        CommonDeclaredNominalInspection.inspect_exact, ih, Models,
        List.mem_cons, forall_eq_or_imp]

inductive SlotAtom : Atom α → Prop where
  | value (first last : α) : SlotAtom (.tyLe (.var first) (.var last))
  | row (first last : α) : SlotAtom (.rowLe (.var first) (.var last))

def AllSlots (atoms : List (Atom α)) : Prop := ∀ atom ∈ atoms, SlotAtom atom

theorem AllSlots.append {first last : List (Atom α)} (left : AllSlots first) (right : AllSlots last) :
    AllSlots (first ++ last) := by
  intro atom member
  exact (List.mem_append.mp member).elim (left atom) (right atom)

private def SlotResult (result : Option (List (Atom α))) : Prop :=
  ∀ atoms, result = some atoms → AllSlots atoms

private theorem append_slots (first last : Option (List (Atom α)))
    (left : SlotResult first) (right : SlotResult last) : SlotResult (append first last) := by
  cases first with
  | none => simp [append, SlotResult]
  | some first =>
      cases last with
      | none => simp [append, SlotResult]
      | some last =>
          simp only [SlotResult, Option.some.injEq, forall_eq'] at left right
          simpa [append, SlotResult] using left.append right

private theorem directions_slots (mode : CommonDeclaredNominalVariance.Variance)
    (first last : Atom α) (left : SlotAtom first) (right : SlotAtom last) :
    AllSlots (CommonDeclaredNominalInspection.directions mode first last) := by
  cases mode <;> simp [AllSlots, CommonDeclaredNominalInspection.directions, left, right]

private theorem inspect_argument_slots (parameter : Parameter) (first last : ArgumentRef α) :
    SlotResult (CommonDeclaredNominalInspection.inspectArgument parameter first.term last.term) := by
  intro atoms returned
  rcases parameter with ⟨kind, mode⟩
  rcases first with ⟨firstKind, first⟩
  rcases last with ⟨lastKind, last⟩
  cases kind <;> cases firstKind <;> cases lastKind <;>
    simp [CommonDeclaredNominalInspection.inspectArgument, ArgumentRef.term,
      CommonDeclaredNominalInspection.termKind] at returned
  all_goals subst atoms
  all_goals apply directions_slots <;> constructor

private theorem inspect_arguments_slots (declaration : Declaration)
    (first last : List (ArgumentRef α)) :
    SlotResult (CommonDeclaredNominalInspection.inspectArguments declaration
      (first.map ArgumentRef.term) (last.map ArgumentRef.term)) := by
  induction declaration generalizing first last with
  | nil => cases first <;> cases last <;>
      simp [CommonDeclaredNominalInspection.inspectArguments, SlotResult, AllSlots]
  | cons parameter rest ih =>
      cases first with
      | nil => cases last <;> simp [CommonDeclaredNominalInspection.inspectArguments, SlotResult]
      | cons first tail =>
          cases last with
          | nil => simp [CommonDeclaredNominalInspection.inspectArguments, SlotResult]
          | cons last suffix =>
              exact append_slots _ _ (inspect_argument_slots parameter first last) (ih tail suffix)

private theorem inspect_slots (registry : Registry) (comparison : Comparison α) :
    SlotResult (inspect registry comparison) := by
  unfold inspect CommonDeclaredNominalInspection.inspect
  split
  · cases found : registry[comparison.1.term.name]? with
    | none => simp [SlotResult]
    | some declaration => exact inspect_arguments_slots declaration comparison.1.arguments comparison.2.arguments
  · simp [SlotResult]

theorem inspect_all_slots (registry : Registry) (comparisons : List (Comparison α))
    (atoms : List (Atom α)) (returned : inspectAll registry comparisons = some atoms) : AllSlots atoms := by
  have result : SlotResult (inspectAll registry comparisons) := by
    clear returned atoms
    induction comparisons with
    | nil => simp [inspectAll, SlotResult, AllSlots]
    | cons comparison rest ih => exact append_slots _ _ (inspect_slots registry comparison) ih
  exact result atoms returned

/-- These are the three syntactic hypotheses of the EXISTING complete
Common bound worklist, proved from the inspector's real output. There is no
condition on any parameter assignment or semantic source type. -/
theorem inspect_all_grammar (registry : Registry) (comparisons : List (Comparison α))
    (atoms : List (Atom α)) (returned : inspectAll registry comparisons = some atoms) :
    PresenceGeneratedChildGrammar.GoodAtoms atoms ∧
      PresenceGeneratedWidth.WidthAtoms atoms ∧
      PresenceSourceConstraintSupport.GoodAtoms atoms := by
  have slots := inspect_all_slots registry comparisons atoms returned
  refine ⟨?_, ?_, ?_⟩
  · intro atom member
    cases slots atom member <;> trivial
  · intro source target member tail required
    cases slots (.tyLe source target) member
    cases required
  · intro atom member
    cases slots atom member <;> trivial

end Yulang.CommonDeclaredNominalSlots
