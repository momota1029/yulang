import Yulang.CommonDeclaredInvariantBounds
import Yulang.CommonDeclaredNominalSourceFamily

/-!
# Existing source families with declared invariant argument bounds

The actual interval inspector appends ordinary inequalities at the original
shared slots. The declared-variance source family then compiles and solves
the whole clause once. No interval centre, extra semantic parameter or
second scalar solver is introduced.

Occurrences are externally supplied finite metadata. Their generation by
nominal source construction/casts remains separate. The source corollaries
remain at the existing presence-generator clause boundary.
-/

namespace Yulang.CommonDeclaredInvariantSourceFamily

open Common (Row)
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (Atom All)
open CommonDeclaredNominalInspection (Registry)
open CommonDeclaredNominalSlots (Comparison)
open CommonDeclaredInvariantBounds (Occurrence inspectAll)
open CommonDeclaredNominalSourceFamily (Scheme AssignmentEquivalent)

variable {slots : Nat}

def Models (registry : Registry) (original : List (Atom (Fin slots)))
    (comparisons : List (Comparison (Fin slots))) (occurrences : List (Occurrence (Fin slots)))
    (assignment : Fin slots → Comp Common.model) : Prop :=
  CommonDeclaredNominalSourceFamily.Models registry original comparisons assignment ∧
    CommonDeclaredInvariantBounds.Models registry occurrences assignment

def solve (registry : Registry) (original : List (Atom (Fin slots)))
    (comparisons : List (Comparison (Fin slots))) (occurrences : List (Occurrence (Fin slots))) :
    List (Scheme slots) :=
  match inspectAll registry occurrences with
  | none => []
  | some bounds => CommonDeclaredNominalSourceFamily.solve registry (original ++ bounds) comparisons

theorem mem_solve (registry : Registry) (original : List (Atom (Fin slots)))
    (comparisons : List (Comparison (Fin slots))) (occurrences : List (Occurrence (Fin slots)))
    (scheme : Scheme slots) :
    scheme ∈ solve registry original comparisons occurrences ↔
      ∃ bounds, inspectAll registry occurrences = some bounds ∧
        scheme ∈ CommonDeclaredNominalSourceFamily.solve registry (original ++ bounds) comparisons := by
  cases found : inspectAll registry occurrences <;> simp [solve, found]

theorem compiled_models_exact (registry : Registry) (original : List (Atom (Fin slots)))
    (comparisons : List (Comparison (Fin slots))) (occurrences : List (Occurrence (Fin slots)))
    (bounds : List (Atom (Fin slots))) (returned : inspectAll registry occurrences = some bounds)
    (assignment : Fin slots → Comp Common.model) :
    CommonDeclaredNominalSourceFamily.Models registry (original ++ bounds) comparisons assignment ↔
      Models registry original comparisons occurrences assignment := by
  have exactBounds : All Common.model assignment bounds ↔
      CommonDeclaredInvariantBounds.Models registry occurrences assignment := by
    simpa [CommonNominalConstraints.Satisfied, returned] using
      CommonDeclaredInvariantBounds.inspect_all_exact registry occurrences assignment
  simp only [Models, CommonDeclaredNominalSourceFamily.Models,
    PresenceNormalForm.all_append, exactBounds]
  exact ⟨fun ⟨⟨originalModel, boundsModel⟩, comparisonsModel⟩ =>
    ⟨⟨originalModel, comparisonsModel⟩, boundsModel⟩,
    fun ⟨⟨originalModel, comparisonsModel⟩, boundsModel⟩ =>
      ⟨⟨originalModel, boundsModel⟩, comparisonsModel⟩⟩

/-- Every unrestricted instance satisfies the original clause, all declared
variance comparisons and every declared-invariant same-actual interval. -/
theorem all_parameters_models (registry : Registry) (original : List (Atom (Fin slots)))
    (comparisons : List (Comparison (Fin slots))) (occurrences : List (Occurrence (Fin slots)))
    (scheme : Scheme slots) (returned : scheme ∈ solve registry original comparisons occurrences)
    (rowParameters : Fin slots → Row) (parameters : scheme.Parameters) :
    Models registry original comparisons occurrences (scheme.instantiate rowParameters parameters) := by
  obtain ⟨bounds, inspected, member⟩ := (mem_solve registry original comparisons occurrences scheme).mp returned
  exact (compiled_models_exact registry original comparisons occurrences bounds inspected _).mp
    (CommonDeclaredNominalSourceFamily.all_parameters_models registry (original ++ bounds) comparisons
      scheme member rowParameters parameters)

end Yulang.CommonDeclaredInvariantSourceFamily
