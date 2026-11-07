import Yulang.CommonNominalRowCells

/-!
# Actual finite pattern compilation for field-template row inequalities

Rows have shared variables, finite signed literal heads, empty and join. All
inequalities, including joins on either side, are interpreted in Common's
arbitrary occurrence-set carrier. Per-occurrence Boolean tables are computed
by a finite truth-table check. They are not supplied by a compatibility oracle.
-/

namespace Yulang.CommonNominalTemplateRowPatterns

open CommonNominalCarrier
open CommonNominalFieldTemplates (TemplateRow)
open CommonNominalRowCells (Pattern Cell)

abbrev Problem (slots : Nat) := List (TemplateRow slots × TemplateRow slots)

def Models (problem : Problem slots) (rows : Fin slots → Row) : Prop :=
  ∀ constraint ∈ problem, Common.rowLe (constraint.1.eval rows) (constraint.2.eval rows)

def literalHeads : TemplateRow slots → List Common.Occurrence
  | .var _ | .empty => []
  | .heads occurrences => occurrences
  | .join first last => literalHeads first ++ literalHeads last

def heads (problem : Problem slots) : List Common.Occurrence :=
  problem.flatMap fun constraint => literalHeads constraint.1 ++ literalHeads constraint.2

def boolEval (occurrence : Option Common.Occurrence) (values : Pattern slots) : TemplateRow slots → Bool
  | .var index => values index
  | .empty => false
  | .heads occurrences => occurrence.any fun value => decide (value ∈ occurrences)
  | .join first last => boolEval occurrence values first || boolEval occurrence values last

theorem bool_eval_exact (term : TemplateRow slots) (rows : Fin slots → Row)
    (values : Pattern slots) (occurrence : Common.Occurrence)
    (same : ∀ index, rows index occurrence ↔ values index = true) :
    term.eval rows occurrence ↔ boolEval (some occurrence) values term = true := by
  induction term with
  | var index => exact same index
  | empty => simp [TemplateRow.eval, Common.rowEmpty, boolEval]
  | heads occurrences => simp only [TemplateRow.eval, boolEval, Option.any_some, decide_eq_true_eq]
  | join first last ihf ihl =>
      simp only [TemplateRow.eval, Common.rowJoin, boolEval, Bool.or_eq_true, ihf, ihl]

theorem outside_eval (term : TemplateRow slots) (values : Pattern slots) (occurrence : Common.Occurrence)
    (absent : occurrence ∉ literalHeads term) :
    boolEval none values term = boolEval (some occurrence) values term := by
  induction term with
  | var | empty => rfl
  | heads occurrences => simp only [literalHeads] at absent; simp [boolEval, absent]
  | join first last ihf ihl =>
      have separate : occurrence ∉ literalHeads first ∧ occurrence ∉ literalHeads last := by
        simpa only [literalHeads, List.mem_append, not_or] using absent
      simp only [boolEval, ihf separate.1, ihl separate.2]

def PatternModels (problem : Problem slots) (occurrence : Option Common.Occurrence) (values : Pattern slots) : Prop :=
  ∀ constraint ∈ problem,
    boolEval occurrence values constraint.1 = true → boolEval occurrence values constraint.2 = true

def check (problem : Problem slots) (occurrence : Option Common.Occurrence) (values : Pattern slots) : Bool :=
  problem.all fun constraint => !boolEval occurrence values constraint.1 || boolEval occurrence values constraint.2

theorem check_exact (problem : Problem slots) (occurrence : Option Common.Occurrence) (values : Pattern slots) :
    check problem occurrence values = true ↔ PatternModels problem occurrence values := by
  simp only [check, List.all_eq_true, PatternModels]
  apply forall_congr'
  intro constraint
  apply forall_congr'
  intro _
  cases boolEval occurrence values constraint.1 <;> cases boolEval occurrence values constraint.2 <;> decide

def patterns (problem : Problem slots) (occurrence : Option Common.Occurrence) : List (Pattern slots) :=
  (Horn.valuations slots).filter (check problem occurrence)

@[simp] theorem mem_patterns (problem : Problem slots) (occurrence : Option Common.Occurrence) (values : Pattern slots) :
    values ∈ patterns problem occurrence ↔ PatternModels problem occurrence values := by
  simp only [patterns, List.mem_filter, Horn.mem_valuations, true_and, check_exact]

def compileCell (problem : Problem slots) (occurrence : Option Common.Occurrence) : Option (Cell slots) :=
  match patterns problem occurrence with
  | [] => none
  | first :: rest => some ⟨first, rest⟩

theorem compiled_patterns (problem : Problem slots) (occurrence : Option Common.Occurrence) (cell : Cell slots)
    (compiled : compileCell problem occurrence = some cell) : cell.patterns = patterns problem occurrence := by
  cases found : patterns problem occurrence with
  | nil => simp [compileCell, found] at compiled
  | cons first rest =>
      have same : cell = ⟨first, rest⟩ := by simpa [compileCell, found] using compiled.symm
      subst cell
      rfl

theorem compile_cell_exact (problem : Problem slots) (occurrence : Option Common.Occurrence) :
    (compileCell problem occurrence).isSome = true ↔ ∃ values, PatternModels problem occurrence values := by
  cases found : patterns problem occurrence with
  | nil =>
      simp only [compileCell, found, Option.isSome_none, Bool.false_eq_true, false_iff, not_exists]
      intro values valid
      have member := (mem_patterns problem occurrence values).mpr valid
      simp [found] at member
  | cons first rest =>
      simp only [compileCell, found, Option.isSome_some, true_iff]
      exact ⟨first, (mem_patterns problem occurrence first).mp (by simp [found])⟩

theorem pattern_models_at (problem : Problem slots) (rows : Fin slots → Row)
    (models : Models problem rows) (occurrence : Common.Occurrence) (values : Pattern slots)
    (same : ∀ index, rows index occurrence ↔ values index = true) :
    PatternModels problem (some occurrence) values := by
  intro constraint present before
  exact (bool_eval_exact constraint.2 rows values occurrence same).mp
    (models constraint present occurrence ((bool_eval_exact constraint.1 rows values occurrence same).mpr before))

theorem pattern_models_outside (problem : Problem slots) (occurrence : Common.Occurrence)
    (absent : occurrence ∉ heads problem) (values : Pattern slots) :
    PatternModels problem none values ↔ PatternModels problem (some occurrence) values := by
  have notIn (constraint : TemplateRow slots × TemplateRow slots) (present : constraint ∈ problem) :
      occurrence ∉ literalHeads constraint.1 ∧ occurrence ∉ literalHeads constraint.2 := by
    constructor
    · intro member
      exact absent (List.mem_flatMap.mpr ⟨constraint, present, List.mem_append.mpr (Or.inl member)⟩)
    · intro member
      exact absent (List.mem_flatMap.mpr ⟨constraint, present, List.mem_append.mpr (Or.inr member)⟩)
  constructor
  · intro valid constraint present
    simpa only [outside_eval constraint.1 values occurrence (notIn constraint present).1,
      outside_eval constraint.2 values occurrence (notIn constraint present).2] using valid constraint present
  · intro valid constraint present
    simpa only [outside_eval constraint.1 values occurrence (notIn constraint present).1,
      outside_eval constraint.2 values occurrence (notIn constraint present).2] using valid constraint present

private theorem bool_empty (term : TemplateRow slots) : boolEval none (fun _ => false) term = false := by
  induction term <;> simp [boolEval, *]

theorem outside_zero_model (problem : Problem slots) : PatternModels problem none (fun _ => false) := by
  intro constraint _ impossible
  simp [bool_empty] at impossible

def outsideCell (problem : Problem slots) : Cell slots :=
  (compileCell problem none).getD ⟨fun _ => false, []⟩

theorem outside_patterns (problem : Problem slots) : (outsideCell problem).patterns = patterns problem none := by
  have existsCell := (compile_cell_exact problem none).mpr ⟨_, outside_zero_model problem⟩
  cases compiled : compileCell problem none with
  | none => simp [compiled] at existsCell
  | some cell =>
      simpa only [outsideCell, compiled, Option.getD_some] using compiled_patterns problem none cell compiled

end Yulang.CommonNominalTemplateRowPatterns
