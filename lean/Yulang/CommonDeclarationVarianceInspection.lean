import Yulang.CommonDeclarationVarianceRegistry
import Yulang.CommonDeclaredNominalSlots

/-!
# Inspecting nominal arguments with source-derived modes

The existing nominal inspector receives exactly the computed source registry.
Its independent comparison judgment below refers only to original headers and
source occurrence/recursion judgments; there is no assumed metadata table.
All original argument terms, including shared type/row slots, are retained.

This is the collapsed-argument head comparison boundary. It does not turn a
head-level theorem into a full recursive nominal carrier theorem.
-/

namespace Yulang.CommonDeclarationVarianceInspection

open CommonDeclarationVarianceSyntax (Program)
open CommonDeclarationVarianceOccurrences (Universe)
open CommonDeclarationVarianceTable (Mode)
open CommonDeclarationVarianceLowering (Header)
open CommonDeclarationVarianceRegistry (modes modes_exact declaration registry)
open CommonNominalHeads (Argument Head)
open CommonNominalConstraints (HeadTerm Satisfied)
open CommonDeclaredNominalInspection (Kind argumentKind)
open Core.PresenceGeneration (Comp)

variable {Index Formal : Type} [DecidableEq Index] [DecidableEq Formal]

def SourceArgument (program : Program Index Formal) (formal : Formal)
    (kind : Kind) (first last : Argument) : Prop :=
  kind = argumentKind first ∧ kind = argumentKind last ∧
    ∃ mode, Mode program formal mode ∧ mode.Rel first last

def SourceArguments (program : Program Index Formal) :
    Header Formal → List Argument → List Argument → Prop
  | [], [], [] => True
  | (kind, formal) :: header, first :: tail, last :: suffix =>
      SourceArgument program formal kind first last ∧ SourceArguments program header tail suffix
  | _, _, _ => False

def SourceSubtype (program : Program Index Formal) (headers : List (Header Formal))
    (first last : Head) : Prop :=
  ∃ header, headers[first.name]? = some header ∧ first.name = last.name ∧
    SourceArguments program header first.arguments last.arguments

theorem argument_exact (program : Program Index Formal) (pool : Universe Index Formal)
    (formal : Formal) (kind : Kind) (first last : Argument) :
    CommonDeclaredNominalInspection.ArgumentRel ⟨kind, modes program pool formal⟩ first last ↔
      SourceArgument program formal kind first last := by
  unfold CommonDeclaredNominalInspection.ArgumentRel SourceArgument
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  constructor
  · intro related
    exact ⟨modes program pool formal, (modes_exact _ _ _ _).mp rfl, related⟩
  · rintro ⟨mode, derived, related⟩
    have selected := (modes_exact program pool formal mode).mpr derived
    simpa only [selected] using related

theorem arguments_exact (program : Program Index Formal) (pool : Universe Index Formal)
    (header : Header Formal) (first last : List Argument) :
    CommonDeclaredNominalInspection.ArgumentsRel (declaration program pool header) first last ↔
      SourceArguments program header first last := by
  induction header generalizing first last with
  | nil => cases first <;> cases last <;>
      simp [declaration, CommonDeclaredNominalInspection.ArgumentsRel, SourceArguments]
  | cons entry rest ih =>
      obtain ⟨kind, formal⟩ := entry
      cases first with
      | nil => cases last <;>
          simp [declaration, CommonDeclaredNominalInspection.ArgumentsRel, SourceArguments]
      | cons first tail =>
          cases last with
          | nil => simp [declaration, CommonDeclaredNominalInspection.ArgumentsRel, SourceArguments]
          | cons last suffix =>
              change CommonDeclaredNominalInspection.ArgumentRel
                ⟨kind, modes program pool formal⟩ first last ∧
                CommonDeclaredNominalInspection.ArgumentsRel (declaration program pool rest) tail suffix ↔ _
              rw [argument_exact, ih]
              rfl

theorem subtype_exact (program : Program Index Formal) (pool : Universe Index Formal)
    (headers : List (Header Formal)) (first last : Head) :
    CommonDeclaredNominalInspection.DeclaredSubtype (registry program pool headers) first last ↔
      SourceSubtype program headers first last := by
  rw [CommonDeclaredNominalInspection.declared_subtype_exact]
  simp only [registry, List.getElem?_map, SourceSubtype]
  cases selected : headers[first.name]? with
  | none => simp
  | some header => simp [arguments_exact]

/-- The real inspector validates nominal identity, lookup, every kind and
arity, then compares in exactly the mode derived from the source equations. -/
theorem inspect_exact (program : Program Index Formal) (pool : Universe Index Formal)
    (headers : List (Header Formal)) (first last : HeadTerm α)
    (assignment : α → Comp Common.model) :
    Satisfied assignment (CommonDeclaredNominalInspection.inspect
      (registry program pool headers) first last) ↔
      SourceSubtype program headers (first.eval assignment) (last.eval assignment) :=
  (CommonDeclaredNominalInspection.inspect_exact _ _ _ _).trans
    (subtype_exact program pool headers _ _)

def Models (program : Program Index Formal) (headers : List (Header Formal))
    (comparisons : List (CommonDeclaredNominalSlots.Comparison α))
    (assignment : α → Comp Common.model) : Prop :=
  ∀ comparison ∈ comparisons,
    SourceSubtype program headers (comparison.1.term.eval assignment) (comparison.2.term.eval assignment)

theorem inspect_all_exact (program : Program Index Formal) (pool : Universe Index Formal)
    (headers : List (Header Formal)) (comparisons : List (CommonDeclaredNominalSlots.Comparison α))
    (assignment : α → Comp Common.model) :
    Satisfied assignment (CommonDeclaredNominalSlots.inspectAll
      (registry program pool headers) comparisons) ↔ Models program headers comparisons assignment := by
  rw [CommonDeclaredNominalSlots.inspect_all_exact]
  unfold CommonDeclaredNominalSlots.Models Models
  exact forall_congr' fun comparison => forall_congr' fun _ => subtype_exact program pool headers _ _

end Yulang.CommonDeclarationVarianceInspection
