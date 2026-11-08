import Yulang.CommonDeclarationVarianceInspection
import Yulang.CommonDeclaredInvariantSourceFamily

/-!
# Original source families using the computed declaration registry

The variance table is computed from original source equations and original
ordered headers before either nominal comparison or invariant attachment.
The independent model judgment uses source occurrence/recursion judgments,
and permits an interval attachment only at a source-invariant formal.

Every produced constraint still enters the existing Common solver once, with
the original shared slots. Unrestricted parameters recover every original
model at this clause boundary. Generation of the comparison/attachment
metadata by nominal expressions and the full nominal carrier remain separate.
-/

namespace Yulang.CommonDeclarationVarianceSourceFamily

open CommonDeclarationVarianceSyntax (Program)
open CommonDeclarationVarianceOccurrences (Universe)
open CommonDeclarationVarianceTable (Mode)
open CommonDeclarationVarianceLowering (Header)
open CommonDeclarationVarianceRegistry (modes modes_exact declaration registry)
open CommonDeclarationVarianceInspection (SourceSubtype subtype_exact)
open CommonDeclaredNominalInspection (Kind)
open CommonDeclaredNominalSlots (Comparison ArgumentRef)
open CommonDeclaredInvariantBounds (Occurrence ArgumentHolds)
open CommonDeclaredNominalSourceFamily (Scheme AssignmentEquivalent)
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (Atom All Clause normalise)

variable {Index Formal : Type} [DecidableEq Index] [DecidableEq Formal]

def SourceBounds (program : Program Index Formal) (headers : List (Header Formal))
    (occurrence : Occurrence α) (assignment : α → Comp Common.model) : Prop :=
  ∃ header kind formal actual,
    headers[occurrence.head.name]? = some header ∧
    header[occurrence.position]? = some (kind, formal) ∧
    occurrence.head.arguments[occurrence.position]? = some actual ∧
    Mode program formal .invariant ∧
    SourceSubtype program headers (occurrence.head.term.eval assignment) (occurrence.head.term.eval assignment) ∧
    ArgumentHolds kind (occurrence.lower.term.eval assignment) (actual.term.eval assignment)
      (occurrence.upper.term.eval assignment)

theorem bounds_exact (program : Program Index Formal) (pool : Universe Index Formal)
    (headers : List (Header Formal)) (occurrence : Occurrence α)
    (assignment : α → Comp Common.model) :
    CommonDeclaredInvariantBounds.Holds (registry program pool headers) occurrence assignment ↔
      SourceBounds program headers occurrence assignment := by
  constructor
  · rintro ⟨⟨parameter, actual⟩, ⟨entry, entryAt, parameterAt, actualAt, invariant⟩, valid, bounded⟩
    have entryAt : (headers[occurrence.head.name]?).map (declaration program pool) = some entry := by
      simpa only [registry, List.getElem?_map] using entryAt
    obtain ⟨header, headerAt, rfl⟩ := Option.map_eq_some_iff.mp entryAt
    have parameterAt : (header[occurrence.position]?).map
        (fun source => (⟨source.1, modes program pool source.2⟩ : CommonDeclaredNominalInspection.Parameter)) =
        some parameter := by
      simpa only [declaration, List.getElem?_map] using parameterAt
    obtain ⟨⟨kind, formal⟩, formalAt, same⟩ := Option.map_eq_some_iff.mp parameterAt
    subst parameter
    exact ⟨header, kind, formal, actual, headerAt, formalAt, actualAt,
      (modes_exact program pool formal .invariant).mp invariant,
      (subtype_exact program pool headers _ _).mp valid, bounded⟩
  · rintro ⟨header, kind, formal, actual, headerAt, formalAt, actualAt, invariant, valid, bounded⟩
    refine ⟨(⟨kind, modes program pool formal⟩, actual), ?_,
      (subtype_exact program pool headers _ _).mpr valid, bounded⟩
    refine ⟨declaration program pool header, ?_, ?_, actualAt,
      (modes_exact program pool formal .invariant).mpr invariant⟩
    · simp only [registry, List.getElem?_map, headerAt, Option.map_some]
    · simp only [declaration, List.getElem?_map, formalAt, Option.map_some]

def Models (program : Program Index Formal) (headers : List (Header Formal))
    (original : List (Atom (Fin slots))) (comparisons : List (Comparison (Fin slots)))
    (occurrences : List (Occurrence (Fin slots))) (assignment : Fin slots → Comp Common.model) : Prop :=
  (All Common.model assignment original ∧
    CommonDeclarationVarianceInspection.Models program headers comparisons assignment) ∧
      ∀ occurrence ∈ occurrences, SourceBounds program headers occurrence assignment

def solve (program : Program Index Formal) (pool : Universe Index Formal)
    (headers : List (Header Formal)) (original : List (Atom (Fin slots)))
    (comparisons : List (Comparison (Fin slots))) (occurrences : List (Occurrence (Fin slots))) :
    List (Scheme slots) :=
  CommonDeclaredInvariantSourceFamily.solve (registry program pool headers) original comparisons occurrences

theorem models_exact (program : Program Index Formal) (pool : Universe Index Formal)
    (headers : List (Header Formal)) (original : List (Atom (Fin slots)))
    (comparisons : List (Comparison (Fin slots))) (occurrences : List (Occurrence (Fin slots)))
    (assignment : Fin slots → Comp Common.model) :
    CommonDeclaredInvariantSourceFamily.Models (registry program pool headers)
      original comparisons occurrences assignment ↔
    Models program headers original comparisons occurrences assignment := by
  unfold CommonDeclaredInvariantSourceFamily.Models CommonDeclaredNominalSourceFamily.Models Models
  apply and_congr
  · apply and_congr_right
    intro _
    unfold CommonDeclaredNominalSlots.Models CommonDeclarationVarianceInspection.Models
    exact forall_congr' fun comparison => forall_congr' fun _ => subtype_exact program pool headers _ _
  · unfold CommonDeclaredInvariantBounds.Models
    exact forall_congr' fun occurrence => forall_congr' fun _ => bounds_exact program pool headers occurrence assignment

theorem all_parameters_models (program : Program Index Formal) (pool : Universe Index Formal)
    (headers : List (Header Formal)) (original : List (Atom (Fin slots)))
    (comparisons : List (Comparison (Fin slots))) (occurrences : List (Occurrence (Fin slots)))
    (scheme : Scheme slots) (returned : scheme ∈ solve program pool headers original comparisons occurrences)
    (rowParameters : Fin slots → Common.Row) (parameters : scheme.Parameters) :
    Models program headers original comparisons occurrences (scheme.instantiate rowParameters parameters) :=
  (models_exact program pool headers original comparisons occurrences _).mp
    (CommonDeclaredInvariantSourceFamily.all_parameters_models _ _ _ _ scheme returned rowParameters parameters)

/-- All original model assignments are recovered; each invariant attachment is
justified by the computed source analysis, not by an assumed metadata mode. -/
theorem solve_all_instances_exact (program : Program Index Formal) (pool : Universe Index Formal)
    (headers : List (Header Formal)) (original : List (Atom (Fin slots)))
    (comparisons : List (Comparison (Fin slots))) (occurrences : List (Occurrence (Fin slots)))
    (child : PresenceGeneratedChildGrammar.GoodAtoms original)
    (width : PresenceGeneratedWidth.WidthAtoms original)
    (rows : PresenceSourceConstraintSupport.GoodAtoms original)
    (assignment : Fin slots → Comp Common.model) :
    Models program headers original comparisons occurrences assignment ↔
      ∃ scheme ∈ solve program pool headers original comparisons occurrences,
        ∃ rowParameters : Fin slots → Common.Row, ∃ parameters : scheme.Parameters,
          AssignmentEquivalent (scheme.instantiate rowParameters parameters) assignment :=
  (models_exact program pool headers original comparisons occurrences assignment).symm.trans
    (CommonDeclaredInvariantSourceFamily.solve_all_instances_exact _ _ _ _ child width rows assignment)

theorem generated_models_exact (expression : Inference.Expr) (clause : Clause (Option Empty))
    (generated : clause ∈ normalise (Core.PresenceGeneration.principal
      ([] : Core.PresenceGeneration.SchemeEnv Empty) expression))
    (program : Program Index Formal) (pool : Universe Index Formal) (headers : List (Header Formal))
    (comparisons : List (Comparison (Fin (clause.locals + 1))))
    (occurrences : List (Occurrence (Fin (clause.locals + 1))))
    (assignment : Fin (clause.locals + 1) → Comp Common.model) :
    Models program headers clause.pack comparisons occurrences assignment ↔
      ∃ scheme ∈ solve program pool headers clause.pack comparisons occurrences,
        ∃ rowParameters : Fin (clause.locals + 1) → Common.Row, ∃ parameters : scheme.Parameters,
          AssignmentEquivalent (scheme.instantiate rowParameters parameters) assignment :=
  (models_exact program pool headers clause.pack comparisons occurrences assignment).symm.trans
    (CommonDeclaredInvariantSourceFamily.generated_models_exact expression clause generated _ _ _ assignment)

end Yulang.CommonDeclarationVarianceSourceFamily
