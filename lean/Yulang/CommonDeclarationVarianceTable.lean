import Yulang.CommonDeclarationVarianceGraph
import Yulang.CommonDeclaredNominalVariance

/-!
# Deriving the declaration variance table

Every output mode is computed from source equations. Usage is the least
signed occurrence judgment; unused parameters take precedence. A used
parameter is invariant exactly when the independent recursive/polarity
judgment marks it. Remaining positive parameters are covariant and remaining
negative parameters contravariant. Both-sign occurrences already seed the
invariant judgment, so the ordering of the two ordinary modes loses no case.

`derive_variance_exact` quantifies over every proposed table and preserves
every original parameter position in the enumeration. Its right side uses
only source judgments, not emitted rules, solver outputs or trusted metadata.
-/

namespace Yulang.CommonDeclarationVarianceTable

open CommonDeclarationVarianceSyntax CommonDeclarationVarianceOccurrences
open CommonDeclarationVarianceCalls CommonDeclarationVarianceGraph
open CommonDeclaredNominalVariance (Variance)

variable {Index Parameter : Type}

theorem ordinary_occurrence (program : Program Index Parameter) (eager : Bool)
    {expression : Expr Index Parameter} {parameter : Parameter} {sign : Bool}
    (derived : Derivation program eager expression parameter sign) :
    Derivation program false expression parameter sign := by
  induction derived with
  | parameter => exact .parameter _
  | reference premise ih => exact .reference ih
  | first premise ih => exact .first ih
  | last premise ih => exact .last ih
  | negative premise ih => exact .negative ih
  | barrier mode premise ih => exact .barrier rfl ih
  | application callee argument ihCallee ihArgument => exact .application ihCallee ihArgument

theorem called_source_used (program : Program Index Parameter) (eager : Bool)
    {expression : Expr Index Parameter} {source target : Parameter}
    (called : Calls program eager expression source target) : Used program false expression source := by
  induction called with
  | reference premise ih => obtain ⟨sign, used⟩ := ih; exact ⟨sign, .reference used⟩
  | first premise ih => obtain ⟨sign, used⟩ := ih; exact ⟨sign, .first used⟩
  | last premise ih => obtain ⟨sign, used⟩ := ih; exact ⟨sign, .last used⟩
  | negative premise ih => obtain ⟨sign, used⟩ := ih; exact ⟨!sign, .negative used⟩
  | barrier mode premise ih => obtain ⟨sign, used⟩ := ih; exact ⟨sign, .barrier rfl used⟩
  | direct callee actual =>
      obtain ⟨direction, callee⟩ := callee
      obtain ⟨sign, actual⟩ := actual
      exact ⟨Bool.xor direction sign, .application callee actual⟩
  | inside callee premise ih =>
      obtain ⟨direction, callee⟩ := callee
      obtain ⟨sign, actual⟩ := ih
      exact ⟨Bool.xor direction sign, .application (ordinary_occurrence _ _ callee) actual⟩

theorem transition_source_used (program : Program Index Parameter) (eager : Bool)
    {expression : Expr Index Parameter} {source : Parameter} {target : Vertex Index Parameter}
    (transition : Transition program eager expression source target) : Used program false expression source := by
  induction transition with
  | reference premise => obtain ⟨sign, used⟩ := premise; exact ⟨sign, .reference used⟩
  | first premise ih => obtain ⟨sign, used⟩ := ih; exact ⟨sign, .first used⟩
  | last premise ih => obtain ⟨sign, used⟩ := ih; exact ⟨sign, .last used⟩
  | negative premise ih => obtain ⟨sign, used⟩ := ih; exact ⟨!sign, .negative used⟩
  | barrier mode premise ih => obtain ⟨sign, used⟩ := ih; exact ⟨sign, .barrier rfl used⟩
  | direct callee actual =>
      obtain ⟨direction, callee⟩ := callee
      obtain ⟨sign, actual⟩ := actual
      exact ⟨Bool.xor direction sign, .application callee actual⟩
  | inside callee premise ih =>
      obtain ⟨direction, callee⟩ := callee
      obtain ⟨sign, actual⟩ := ih
      exact ⟨Bool.xor direction sign, .application (ordinary_occurrence _ _ callee) actual⟩

theorem reason_used (program : Program Index Parameter) (state : State Index Parameter)
    (reason : Reason program state) :
    match state with
    | .inl _ => True
    | .inr vertex => Used program false (program.body vertex.1) vertex.2 := by
  induction reason with
  | reflexive => trivial
  | path => trivial
  | cycle called _ _ => exact transition_source_used _ _ called
  | mixed positive _ => exact ⟨false, positive⟩
  | propagate called _ _ => exact transition_source_used _ _ called

def Mode (program : Program Index Parameter) (parameter : Parameter) : Variance → Prop
  | .unused => ¬ Used program false (program.body (program.root parameter)) parameter
  | .invariant => Used program false (program.body (program.root parameter)) parameter ∧
      Reason program (.inr (program.root parameter, parameter))
  | .covariant => Derivation program false (program.body (program.root parameter)) parameter false ∧
      ¬ Reason program (.inr (program.root parameter, parameter))
  | .contravariant => Derivation program false (program.body (program.root parameter)) parameter true ∧
      ¬ Derivation program false (program.body (program.root parameter)) parameter false ∧
      ¬ Reason program (.inr (program.root parameter, parameter))

theorem covariant_has_no_negative (program : Program Index Parameter) (parameter : Parameter)
    (mode : Mode program parameter .covariant) :
    ¬ Derivation program false (program.body (program.root parameter)) parameter true :=
  fun negative => mode.2 (.mixed mode.1 negative)

theorem invariant_propagates (program : Program Index Parameter) (first next : Parameter)
    (called : Transition program false (program.body (program.root first)) first (program.root next, next))
    (mode : Mode program next .invariant) : Mode program first .invariant :=
  ⟨transition_source_used _ _ called, .propagate called mode.2⟩

def classify : Bool → Bool → Bool → Variance
  | false, false, _ => .unused
  | _, _, true => .invariant
  | true, _, false => .covariant
  | false, true, false => .contravariant

private theorem classify_exact (positive negative blocked : Bool) (mode : Variance) :
    classify positive negative blocked = mode ↔
      match mode with
      | .unused => ¬ (positive = true ∨ negative = true)
      | .invariant => (positive = true ∨ negative = true) ∧ blocked = true
      | .covariant => positive = true ∧ blocked ≠ true
      | .contravariant => negative = true ∧ positive ≠ true ∧ blocked ≠ true := by
  cases positive <;> cases negative <;> cases blocked <;> cases mode <;> decide

variable [DecidableEq Index] [DecidableEq Parameter]

def modeFrom (program : Program Index Parameter) (signs : List (Fact Index Parameter))
    (blocked : List (State Index Parameter)) (parameter : Parameter) : Variance :=
  classify (decide ((program.root parameter, parameter, false) ∈ signs))
    (decide ((program.root parameter, parameter, true) ∈ signs)) (decide (.inr (program.root parameter, parameter) ∈ blocked))

theorem mode_from_exact (program : Program Index Parameter) (pool : Universe Index Parameter)
    (parameter : Parameter) (mode : Variance) :
    modeFrom program (occurrences program false pool) (analyze program pool) parameter = mode ↔
      Mode program parameter mode := by
  have use : Used program false (program.body (program.root parameter)) parameter ↔
      Derivation program false (program.body (program.root parameter)) parameter false ∨
      Derivation program false (program.body (program.root parameter)) parameter true := by
    constructor
    · rintro ⟨sign, derived⟩
      cases sign
      · exact Or.inl derived
      · exact Or.inr derived
    · intro derived
      exact derived.elim (fun positive => ⟨false, positive⟩) (fun negative => ⟨true, negative⟩)
  unfold modeFrom
  rw [classify_exact]
  cases mode <;> simp only [Mode, use, ne_eq, decide_eq_true_eq, occurrences_exact, analyze_exact]

def TableJudgment (program : Program Index Parameter) : List Parameter → List (Parameter × Variance) → Prop
  | [], [] => True
  | parameter :: parameters, (original, mode) :: table =>
      parameter = original ∧ Mode program parameter mode ∧ TableJudgment program parameters table
  | _, _ => False

def deriveVariance (program : Program Index Parameter) (pool : Universe Index Parameter) :
    List (Parameter × Variance) :=
  let signs := occurrences program false pool
  let blocked := analyze program pool
  pool.parameters.map fun parameter => (parameter, modeFrom program signs blocked parameter)

theorem derive_variance_exact (program : Program Index Parameter) (pool : Universe Index Parameter)
    (table : List (Parameter × Variance)) :
    deriveVariance program pool = table ↔ TableJudgment program pool.parameters table := by
  have pointwise := mode_from_exact program pool
  unfold deriveVariance
  induction pool.parameters generalizing table with
  | nil => cases table <;> simp [TableJudgment]
  | cons parameter parameters ih =>
      cases table with
      | nil => simp [TableJudgment]
      | cons entry table =>
          obtain ⟨original, mode⟩ := entry
          simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq, TableJudgment, ih]
          constructor
          · rintro ⟨⟨same, selected⟩, tail⟩
            exact ⟨same, (pointwise _ _).mp selected, tail⟩
          · rintro ⟨same, selected, tail⟩
            exact ⟨⟨same, (pointwise _ _).mpr selected⟩, tail⟩

theorem derive_variance_retains_parameters (program : Program Index Parameter) (pool : Universe Index Parameter) :
    (deriveVariance program pool).map Prod.fst = pool.parameters := by
  simp only [deriveVariance, List.map_map, Function.comp_def]
  exact List.map_id pool.parameters

end Yulang.CommonDeclarationVarianceTable
