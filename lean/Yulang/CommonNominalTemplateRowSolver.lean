import Yulang.CommonNominalTemplateRowPatterns

/-!
# Unrestricted all-model families for finite field-template row constraints

The solver computes a finite membership-vector table at every literal signed
head and one table for all other occurrences. Schemes contain only those
finite tables. Instantiation selects table entries using arbitrary parameter
rows, without consulting the original problem or imposing a model predicate.

This allows joins on both sides, finite nonempty upper bounds, invariant row
equalities and pure bounds. Selection uses finite Boolean partition masks;
these are internal set expressions, not new surface row syntax or exports.
Signed transforms and general type bounds remain outside this module.
-/

namespace Yulang.CommonNominalTemplateRowSolver

open CommonNominalCarrier
open CommonNominalFieldTemplates (TemplateRow)
open CommonNominalRowCells (Pattern Cell Parameters recoveryParameters)
open CommonNominalTemplateRowPatterns (Problem Models PatternModels patterns heads compileCell outsideCell)

def lookup : List (Common.Occurrence × Cell slots) → Common.Occurrence → Option (Cell slots)
  | [], _ => none
  | (head, cell) :: rest, occurrence => if occurrence = head then some cell else lookup rest occurrence

private theorem lookup_some (entries : List (Common.Occurrence × Cell slots)) (occurrence : Common.Occurrence)
    (cell : Cell slots) (found : lookup entries occurrence = some cell) : (occurrence, cell) ∈ entries := by
  induction entries with
  | nil => simp [lookup] at found
  | cons entry rest ih =>
      rcases entry with ⟨head, value⟩
      by_cases same : occurrence = head
      · have cellSame : value = cell := by simpa [lookup, same] using found
        subst head; subst cell
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih (by simpa [lookup, same] using found))

private theorem lookup_none (entries : List (Common.Occurrence × Cell slots)) (occurrence : Common.Occurrence)
    (absent : lookup entries occurrence = none) : occurrence ∉ entries.map Prod.fst := by
  induction entries with
  | nil => simp
  | cons entry rest ih =>
      rcases entry with ⟨head, cell⟩
      by_cases same : occurrence = head
      · simp [lookup, same] at absent
      · simpa only [List.map_cons, List.mem_cons, not_or] using
          And.intro same (ih (by simpa [lookup, same] using absent))

def compileEntries (problem : Problem slots) :
    List Common.Occurrence → Option (List (Common.Occurrence × Cell slots))
  | [] => some []
  | head :: rest =>
      match compileCell problem (some head), compileEntries problem rest with
      | some cell, some entries => some ((head, cell) :: entries)
      | _, _ => none

theorem compile_entries_sound (problem : Problem slots) (original : List Common.Occurrence)
    (entries : List (Common.Occurrence × Cell slots)) (compiled : compileEntries problem original = some entries) :
    entries.map Prod.fst = original ∧
      ∀ pair ∈ entries, pair.2.patterns = patterns problem (some pair.1) := by
  induction original generalizing entries with
  | nil =>
      have same : entries = [] := by simpa [compileEntries] using compiled.symm
      subst entries
      exact ⟨rfl, by simp⟩
  | cons head rest ih =>
      cases first : compileCell problem (some head) with
      | none => simp [compileEntries, first] at compiled
      | some cell =>
          cases tail : compileEntries problem rest with
          | none => simp [compileEntries, first, tail] at compiled
          | some remaining =>
              have same : entries = (head, cell) :: remaining := by
                simpa [compileEntries, first, tail] using compiled.symm
              subst entries
              obtain ⟨keysSame, sound⟩ := ih remaining tail
              refine ⟨by simp only [List.map_cons, keysSame], ?_⟩
              intro pair present
              rcases List.mem_cons.mp present with same | present
              · subst pair
                exact CommonNominalTemplateRowPatterns.compiled_patterns problem (some head) cell first
              · exact sound pair present

theorem compile_entries_complete (problem : Problem slots) (rows : Fin slots → Row)
    (models : Models problem rows) (original : List Common.Occurrence) :
    ∃ entries, compileEntries problem original = some entries := by
  classical
  induction original with
  | nil => exact ⟨[], rfl⟩
  | cons head rest ih =>
      let values : Pattern slots := fun index => decide (rows index head)
      have valid := CommonNominalTemplateRowPatterns.pattern_models_at problem rows models head values
        (by intro index; simp only [values, decide_eq_true_eq])
      have succeeds := (CommonNominalTemplateRowPatterns.compile_cell_exact problem (some head)).mpr ⟨values, valid⟩
      cases first : compileCell problem (some head) with
      | none => simp [first] at succeeds
      | some cell =>
          obtain ⟨entries, compiled⟩ := ih
          exact ⟨(head, cell) :: entries, by simp only [compileEntries, first, compiled]⟩

structure Scheme (slots : Nat) where
  outside : Cell slots
  entries : List (Common.Occurrence × Cell slots)

abbrev Scheme.Parameters (_scheme : Scheme slots) := CommonNominalRowCells.Parameters slots

def Scheme.cellFor (scheme : Scheme slots) (occurrence : Common.Occurrence) : Cell slots :=
  (lookup scheme.entries occurrence).getD scheme.outside

def Scheme.instantiate (scheme : Scheme slots) (parameters : scheme.Parameters) : Fin slots → Row :=
  fun index occurrence => (scheme.cellFor occurrence).instantiate parameters index occurrence

def solve (problem : Problem slots) : List (Scheme slots) :=
  match compileEntries problem (heads problem) with
  | none => []
  | some entries => [⟨outsideCell problem, entries⟩]

private theorem returned (problem : Problem slots) (scheme : Scheme slots) (member : scheme ∈ solve problem) :
    ∃ entries, compileEntries problem (heads problem) = some entries ∧ scheme = ⟨outsideCell problem, entries⟩ := by
  cases compiled : compileEntries problem (heads problem) with
  | none => simp [solve, compiled] at member
  | some entries => exact ⟨entries, rfl, by simpa [solve, compiled] using member⟩

theorem selected_patterns_exact (problem : Problem slots) (scheme : Scheme slots) (member : scheme ∈ solve problem)
    (occurrence : Common.Occurrence) (values : Pattern slots) :
    values ∈ (scheme.cellFor occurrence).patterns ↔ PatternModels problem (some occurrence) values := by
  obtain ⟨entries, compiled, rfl⟩ := returned problem scheme member
  obtain ⟨keysSame, sound⟩ := compile_entries_sound problem (heads problem) entries compiled
  cases found : lookup entries occurrence with
  | some cell =>
      simp only [Scheme.cellFor, found, Option.getD_some]
      rw [sound (occurrence, cell) (lookup_some entries occurrence cell found)]
      exact CommonNominalTemplateRowPatterns.mem_patterns problem (some occurrence) values
  | none =>
      have absent : occurrence ∉ heads problem := by
        simpa only [keysSame] using lookup_none entries occurrence found
      simp only [Scheme.cellFor, found, Option.getD_none, CommonNominalTemplateRowPatterns.outside_patterns]
      exact (CommonNominalTemplateRowPatterns.mem_patterns problem none values).trans
        (CommonNominalTemplateRowPatterns.pattern_models_outside problem occurrence absent values)

/-- Every row parameter is arbitrary, including infinite sets. The finite
compiled tables discharge all original constraints without a residual check. -/
theorem all_parameters_models (problem : Problem slots) (scheme : Scheme slots)
    (member : scheme ∈ solve problem) (parameters : scheme.Parameters) :
    Models problem (scheme.instantiate parameters) := by
  intro constraint present occurrence before
  obtain ⟨values, included, same⟩ := (scheme.cellFor occurrence).selects parameters occurrence
  have valid := (selected_patterns_exact problem scheme member occurrence values).mp included
  exact (CommonNominalTemplateRowPatterns.bool_eval_exact constraint.2 (scheme.instantiate parameters)
    values occurrence same).mpr
    (valid constraint present ((CommonNominalTemplateRowPatterns.bool_eval_exact constraint.1
      (scheme.instantiate parameters) values occurrence same).mp before))

/-- The original rows themselves give one unrestricted parameter vector
that recovers all original slots literally, simultaneously at every head. -/
theorem model_retraction (problem : Problem slots) (scheme : Scheme slots) (member : scheme ∈ solve problem)
    (rows : Fin slots → Row) (models : Models problem rows) :
    scheme.instantiate (recoveryParameters rows) = rows := by
  classical
  funext index occurrence
  apply propext
  let values : Pattern slots := fun slot => decide (rows slot occurrence)
  have same : ∀ slot, rows slot occurrence ↔ values slot = true := by
    intro slot; simp only [values, decide_eq_true_eq]
  have valid := CommonNominalTemplateRowPatterns.pattern_models_at problem rows models occurrence values same
  exact (scheme.cellFor occurrence).recovers rows occurrence
    ⟨values, (selected_patterns_exact problem scheme member occurrence values).mpr valid, same⟩ index

theorem solve_all_instances_exact (problem : Problem slots) (rows : Fin slots → Row) :
    Models problem rows ↔ ∃ scheme ∈ solve problem, ∃ parameters : scheme.Parameters,
      scheme.instantiate parameters = rows := by
  constructor
  · intro models
    obtain ⟨entries, compiled⟩ := compile_entries_complete problem rows models (heads problem)
    let scheme : Scheme slots := ⟨outsideCell problem, entries⟩
    have member : scheme ∈ solve problem := by simp only [solve, compiled, List.mem_singleton]; rfl
    exact ⟨scheme, member, recoveryParameters rows, model_retraction problem scheme member rows models⟩
  · rintro ⟨scheme, member, parameters, same⟩
    exact same ▸ all_parameters_models problem scheme member parameters

theorem pure_row_empty (problem : Problem slots) (scheme : Scheme slots) (member : scheme ∈ solve problem)
    (parameters : scheme.Parameters) (index : Fin slots)
    (pure : (TemplateRow.var index, TemplateRow.empty) ∈ problem) :
    scheme.instantiate parameters index = Common.rowEmpty :=
  Common.rowLe_antisymm (all_parameters_models problem scheme member parameters _ pure)
    (Common.rowEmpty_le _)

end Yulang.CommonNominalTemplateRowSolver
