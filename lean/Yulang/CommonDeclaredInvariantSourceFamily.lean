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
open PresenceNormalForm (Atom All Clause normalise)
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

private theorem inspected_grammar (registry : Registry) (occurrences : List (Occurrence α))
    (atoms : List (Atom α)) (returned : inspectAll registry occurrences = some atoms) :
    PresenceGeneratedChildGrammar.GoodAtoms atoms ∧ PresenceGeneratedWidth.WidthAtoms atoms ∧
      PresenceSourceConstraintSupport.GoodAtoms atoms := by
  have sharedSlots := CommonDeclaredInvariantBounds.inspect_all_slots registry occurrences atoms returned
  refine ⟨?_, ?_, ?_⟩
  · intro atom member
    cases sharedSlots atom member <;> trivial
  · intro source target member tail required
    cases sharedSlots (.tyLe source target) member
    cases required
  · intro atom member
    cases sharedSlots atom member <;> trivial

/-- Every original model is recovered simultaneously at every original
slot. Only the original clause has syntactic premises; the two inspectors'
outputs satisfy the existing solver grammar by construction. -/
theorem solve_all_instances_exact (registry : Registry) (original : List (Atom (Fin slots)))
    (comparisons : List (Comparison (Fin slots))) (occurrences : List (Occurrence (Fin slots)))
    (child : PresenceGeneratedChildGrammar.GoodAtoms original)
    (width : PresenceGeneratedWidth.WidthAtoms original)
    (rows : PresenceSourceConstraintSupport.GoodAtoms original)
    (assignment : Fin slots → Comp Common.model) :
    Models registry original comparisons occurrences assignment ↔
      ∃ scheme ∈ solve registry original comparisons occurrences,
        ∃ rowParameters : Fin slots → Row, ∃ parameters : scheme.Parameters,
          AssignmentEquivalent (scheme.instantiate rowParameters parameters) assignment := by
  constructor
  · intro model
    obtain ⟨bounds, inspected, _⟩ :=
      (CommonDeclaredInvariantBounds.inspect_all_exact registry occurrences assignment).mpr model.2
    obtain ⟨boundsChild, boundsWidth, boundsRows⟩ := inspected_grammar registry occurrences bounds inspected
    have compiledModel := (compiled_models_exact registry original comparisons occurrences bounds inspected assignment).mpr model
    obtain ⟨scheme, member, rowParameters, parameters, same⟩ :=
      (CommonDeclaredNominalSourceFamily.solve_all_instances_exact registry (original ++ bounds) comparisons
        (child.append boundsChild) (width.append boundsWidth) (rows.append boundsRows) assignment).mp compiledModel
    exact ⟨scheme, (mem_solve registry original comparisons occurrences scheme).mpr ⟨bounds, inspected, member⟩,
      rowParameters, parameters, same⟩
  · rintro ⟨scheme, returned, rowParameters, parameters, same⟩
    obtain ⟨bounds, inspected, member⟩ := (mem_solve registry original comparisons occurrences scheme).mp returned
    obtain ⟨boundsChild, boundsWidth, boundsRows⟩ := inspected_grammar registry occurrences bounds inspected
    apply (compiled_models_exact registry original comparisons occurrences bounds inspected assignment).mp
    exact (CommonDeclaredNominalSourceFamily.solve_all_instances_exact registry (original ++ bounds) comparisons
      (child.append boundsChild) (width.append boundsWidth) (rows.append boundsRows) assignment).mpr
        ⟨scheme, member, rowParameters, parameters, same⟩

/-- Actual clauses from the existing inference source generator discharge
all original-clause grammar premises. Occurrence provenance is still external. -/
theorem generated_models_exact (expression : Inference.Expr) (clause : Clause (Option Empty))
    (generated : clause ∈ normalise (Core.PresenceGeneration.principal
      ([] : Core.PresenceGeneration.SchemeEnv Empty) expression))
    (registry : Registry) (comparisons : List (Comparison (Fin (clause.locals + 1))))
    (occurrences : List (Occurrence (Fin (clause.locals + 1))))
    (assignment : Fin (clause.locals + 1) → Comp Common.model) :
    Models registry clause.pack comparisons occurrences assignment ↔
      ∃ scheme ∈ solve registry clause.pack comparisons occurrences,
        ∃ rowParameters : Fin (clause.locals + 1) → Row, ∃ parameters : scheme.Parameters,
          AssignmentEquivalent (scheme.instantiate rowParameters parameters) assignment :=
  solve_all_instances_exact registry clause.pack comparisons occurrences
    (PresenceGeneratedChildGrammar.generated_child_grammar expression clause generated)
    (PresenceGeneratedWidth.generated_width_atoms expression clause generated)
    (PresenceSourceConstraintSupport.generated_row_shapes expression clause generated) assignment

end Yulang.CommonDeclaredInvariantSourceFamily
