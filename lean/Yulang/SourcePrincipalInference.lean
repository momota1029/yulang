import Yulang.JointConstraintInference
import Yulang.SourceConstraintSupport

/-!
# Principal inference from the original closed source expressions

The entry starts at `Inference.Expr`, generates the original principal
formula, normalizes its finite alternatives, and actually solves their type
and row constraints. It receives no type graph, row assignment, guessed
solution, successful cache, or fuel from its caller.

Every retained alternative is a finite regular scheme with free value and
row parameters. An unsupported alternative is reported separately, rather
than silently discarded. The value-restricted let's original alternatives
and captured slots are preserved throughout.
-/

namespace Yulang.SourcePrincipalInference

open Inference ConstraintNormalForm

universe u

variable {Row : Type u}

abbrev model := @JointConstraintInference.model

structure Alternative where
  slots : Nat
  scheme : JointConstraintInference.Scheme slots
  output : Fin slots

def Alternative.ofClause (clause : Clause (Option Empty))
    (scheme : JointConstraintInference.Scheme (clause.locals + 1)) : Alternative :=
  ⟨clause.locals + 1, scheme, Fin.last clause.locals⟩

def Alternative.Instance (algebra : RowFlowSchemes.Algebra Row)
    (alternative : Alternative) (target : Comp (model algebra)) : Prop :=
  alternative.scheme.Instance algebra alternative.output target

abbrev Principal := List Alternative

def Principal.Instance (algebra : RowFlowSchemes.Algebra Row)
    (principal : Principal) (target : Comp (model algebra)) : Prop :=
  ∃ alternative ∈ principal, alternative.Instance algebra target

/-- A missing result means unsupported syntax. A present empty list means
that all alternatives were proved inconsistent. -/
def collect : List (Clause (Option Empty)) → Option Principal
  | [] => some []
  | clause :: rest =>
      match JointConstraintInference.infer (ConstraintProblems.split clause.pack) with
      | .unsupported => none
      | .rejected => collect rest
      | .inferred scheme => (collect rest).map (Alternative.ofClause clause scheme :: ·)

def clauses (expression : Expr) : List (Clause (Option Empty)) :=
  normalise (principal ([] : SchemeEnv Empty) expression)

inductive Status where
  | unsupported
  | rejected
  | inferred
  deriving DecidableEq, Repr

inductive Result where
  | unsupported
  | rejected
  | inferred : Principal → Result

def Result.status : Result → Status
  | .unsupported => .unsupported
  | .rejected => .rejected
  | .inferred _ => .inferred

def Result.Instance (algebra : RowFlowSchemes.Algebra Row)
    (target : Comp (model algebra)) : Result → Prop
  | .inferred principal => principal.Instance algebra target
  | _ => False

/-- Total inference directly from a closed core expression. The finite
alternatives keep all value-let instances; no arbitrary branch is selected. -/
def infer (expression : Expr) : Result :=
  if expression.requiredFieldsOnly then
    match collect (clauses expression) with
    | none => .unsupported
    | some [] => .rejected
    | some (first :: rest) => .inferred (first :: rest)
  else .unsupported

def supported (expression : Expr) : Bool :=
  expression.requiredFieldsOnly &&
    (clauses expression).all fun clause =>
      JointConstraintInference.supported (ConstraintProblems.split clause.pack)

private theorem joint_supported_of_status (problem : ConstraintProblems.Problem n)
    (supportedStatus : (JointConstraintInference.infer problem).status ≠ .unsupported) :
    JointConstraintInference.supported problem = true := by
  cases checked : JointConstraintInference.supported problem with
  | false => exact False.elim (supportedStatus ((JointConstraintInference.infer_unsupported_iff problem).mpr checked))
  | true => rfl

theorem collect_none_iff (clauses : List (Clause (Option Empty))) :
    collect clauses = none ↔
      ∃ clause ∈ clauses, JointConstraintInference.supported (ConstraintProblems.split clause.pack) = false := by
  induction clauses with
  | nil => simp [collect]
  | cons clause rest ih =>
      cases returned : JointConstraintInference.infer (ConstraintProblems.split clause.pack) with
      | unsupported =>
          have absent := (JointConstraintInference.infer_unsupported_iff
            (ConstraintProblems.split clause.pack)).mp (by rw [returned]; rfl)
          simp [collect, returned, absent]
      | rejected =>
          have checked := joint_supported_of_status (ConstraintProblems.split clause.pack)
            (by rw [returned]; simp [JointConstraintInference.Result.status])
          simp [collect, returned, checked, ih]
      | inferred scheme =>
          have checked := joint_supported_of_status (ConstraintProblems.split clause.pack)
            (by rw [returned]; simp [JointConstraintInference.Result.status])
          simp [collect, returned, checked, ih]

theorem collect_some_supported (clauses : List (Clause (Option Empty))) (result : Principal)
    (returned : collect clauses = some result) :
    ∀ clause ∈ clauses, JointConstraintInference.supported (ConstraintProblems.split clause.pack) = true := by
  intro clause member
  cases checked : JointConstraintInference.supported (ConstraintProblems.split clause.pack) with
  | false =>
      have absent := (collect_none_iff clauses).mpr ⟨clause, member, checked⟩
      rw [returned] at absent
      cases absent
  | true => rfl

/-- Exactness of the computed finite family. Rejected branches contribute
no instances, while every successful branch keeps all its free parameters. -/
theorem collect_instances_exact (algebra : RowFlowSchemes.Algebra Row)
    (rowAntisymm : ∀ {left right}, algebra.le left right → algebra.le right left → left = right)
    (clauses : List (Clause (Option Empty))) (result : Principal)
    (returned : collect clauses = some result) (target : Comp (model algebra)) :
    result.Instance algebra target ↔
      ∃ clause ∈ clauses,
        (ConstraintProblems.split clause.pack).Instance (model algebra) (Fin.last clause.locals) target := by
  induction clauses generalizing result with
  | nil =>
      have equal : result = [] := (Option.some.inj returned).symm
      subst result
      simp [Principal.Instance]
  | cons clause rest ih =>
      have checked := collect_some_supported (clause :: rest) result returned clause List.mem_cons_self
      have exactHead := JointConstraintInference.infer_instances_exact algebra rowAntisymm
        (ConstraintProblems.split clause.pack) checked (Fin.last clause.locals) target
      cases solved : JointConstraintInference.infer (ConstraintProblems.split clause.pack) with
      | unsupported => simp [collect, solved] at returned
      | rejected =>
          have tail : collect rest = some result := by simpa only [collect, solved] using returned
          have absent : ¬ (ConstraintProblems.split clause.pack).Instance (model algebra)
              (Fin.last clause.locals) target := by
            intro accepted
            have impossible := exactHead.mp accepted
            simp [solved, JointConstraintInference.Result.Instance] at impossible
          rw [ih result tail]
          constructor
          · rintro ⟨choice, member, accepted⟩
            exact ⟨choice, List.mem_cons_of_mem _ member, accepted⟩
          · rintro ⟨choice, member, accepted⟩
            rcases List.mem_cons.mp member with rfl | member
            · exact False.elim (absent accepted)
            · exact ⟨choice, member, accepted⟩
      | inferred scheme =>
          cases tail : collect rest with
          | none => simp [collect, solved, tail] at returned
          | some alternatives =>
              have equal : result = Alternative.ofClause clause scheme :: alternatives :=
                (Option.some.inj (by simpa [collect, solved, tail] using returned)).symm
              subst result
              have headExact : (Alternative.ofClause clause scheme).Instance algebra target ↔
                  (ConstraintProblems.split clause.pack).Instance (model algebra)
                    (Fin.last clause.locals) target := by
                simpa [solved, JointConstraintInference.Result.Instance,
                  Alternative.Instance, Alternative.ofClause] using exactHead.symm
              constructor
              · rintro ⟨alternative, member, accepted⟩
                rcases List.mem_cons.mp member with rfl | member
                · exact ⟨clause, List.mem_cons_self, headExact.mp accepted⟩
                · obtain ⟨choice, present, held⟩ := (ih alternatives tail).mp ⟨alternative, member, accepted⟩
                  exact ⟨choice, List.mem_cons_of_mem _ present, held⟩
              · rintro ⟨choice, member, accepted⟩
                rcases List.mem_cons.mp member with rfl | member
                · exact ⟨_, List.mem_cons_self, headExact.mpr accepted⟩
                · obtain ⟨alternative, present, held⟩ := (ih alternatives tail).mpr ⟨choice, member, accepted⟩
                  exact ⟨alternative, List.mem_cons_of_mem _ present, held⟩

theorem infer_unsupported_iff (expression : Expr) :
    (infer expression).status = .unsupported ↔ supported expression = false := by
  cases sourceChecked : expression.requiredFieldsOnly with
  | false => simp [infer, supported, sourceChecked, Result.status]
  | true =>
      have absent := collect_none_iff (clauses expression)
      cases returned : collect (clauses expression) with
      | none =>
          obtain ⟨clause, member, unsupported⟩ := absent.mp returned
          have failed : supported expression = false := by
            apply Bool.eq_false_iff.mpr
            intro accepted
            have all := List.all_eq_true.mp (Bool.and_eq_true_iff.mp accepted).2 clause member
            rw [unsupported] at all
            cases all
          simp [infer, sourceChecked, returned, Result.status, failed]
      | some result =>
          have checked : supported expression = true :=
            Bool.and_eq_true_iff.mpr ⟨sourceChecked,
              List.all_eq_true.mpr (collect_some_supported (clauses expression) result returned)⟩
          cases result <;> simp [infer, sourceChecked, returned, Result.status, checked]

/-- The required-field solver explicitly declines optional-field syntax,
including when it occurs inside another expression. -/
theorem infer_optional_unsupported (expression : Expr)
    (optional : expression.requiredFieldsOnly = false) : infer expression = .unsupported := by
  simp [infer, optional]

/-- All instances of the actual inference result are exactly the original
declarative typings, provided only the executable support check succeeds. -/
theorem infer_instances_exact (algebra : RowFlowSchemes.Algebra Row)
    (rowAntisymm : ∀ {left right}, algebra.le left right → algebra.le right left → left = right)
    (expression : Expr) (checked : supported expression = true) (target : Comp (model algebra)) :
    (infer expression).Instance algebra target ↔ Typing (model algebra) [] expression target := by
  have sourceChecked := (Bool.and_eq_true_iff.mp checked).1
  rw [ConstraintProblems.closed_source_problems_exact (model algebra)
    (RegularInferenceModel.subtype_refl algebra.le) RegularInferenceModel.subtype_trans
    algebra.refl algebra.trans expression target]
  change (infer expression).Instance algebra target ↔
    ∃ clause ∈ clauses expression,
      (ConstraintProblems.split clause.pack).Instance (model algebra) (Fin.last clause.locals) target
  cases returned : collect (clauses expression) with
  | none =>
      have failed := (infer_unsupported_iff expression).mp
        (by simp [infer, sourceChecked, returned, Result.status])
      rw [checked] at failed
      cases failed
  | some result =>
      have exact := collect_instances_exact algebra rowAntisymm (clauses expression) result returned target
      cases result with
      | nil => simpa only [infer, sourceChecked, ↓reduceIte, returned, Result.Instance, Principal.Instance,
          List.not_mem_nil, false_and, exists_false] using exact
      | cons first rest => simpa only [infer, sourceChecked, ↓reduceIte, returned, Result.Instance] using exact

/-- A returned principal family represents every original result type and
row. The only operational premise names the actual computed return value. -/
theorem infer_inferred_exact (algebra : RowFlowSchemes.Algebra Row)
    (rowAntisymm : ∀ {left right}, algebra.le left right → algebra.le right left → left = right)
    (expression : Expr) (result : Principal) (returned : infer expression = .inferred result)
    (target : Comp (model algebra)) :
    result.Instance algebra target ↔ Typing (model algebra) [] expression target := by
  have checked : supported expression = true := by
    cases accepted : supported expression with
    | false =>
        have failed := (infer_unsupported_iff expression).mpr accepted
        simp [returned, Result.status] at failed
    | true => rfl
  simpa [returned, Result.Instance] using infer_instances_exact algebra rowAntisymm expression checked target

theorem infer_rejected_sound (algebra : RowFlowSchemes.Algebra Row)
    (rowAntisymm : ∀ {left right}, algebra.le left right → algebra.le right left → left = right)
    (expression : Expr) (returned : infer expression = .rejected) :
    ¬ ∃ target, Typing (model algebra) [] expression target := by
  have checked : supported expression = true := by
    cases accepted : supported expression with
    | false =>
        have failed := (infer_unsupported_iff expression).mpr accepted
        simp [returned, Result.status] at failed
    | true => rfl
  rintro ⟨target, typed⟩
  have accepted := (infer_instances_exact algebra rowAntisymm expression checked target).mpr typed
  simp [returned, Result.Instance] at accepted

theorem Alternative.instance_of_parameters (algebra : RowFlowSchemes.Algebra Row)
    (alternative : Alternative) (rowParameter : Fin alternative.slots → Row)
    (valueParameter : Fin alternative.scheme.size → JointConstraintInference.Value Row) :
    alternative.Instance algebra
      (alternative.scheme.instantiate algebra rowParameter valueParameter alternative.output) :=
  ⟨rowParameter, valueParameter, RegularInferenceModel.subtype_refl algebra.le _, algebra.refl _⟩

theorem infer_inferred_nonempty (expression : Expr) (result : Principal)
    (returned : infer expression = .inferred result) : result ≠ [] := by
  have sourceChecked : expression.requiredFieldsOnly = true := by
    cases checked : expression.requiredFieldsOnly with
    | false => simp [infer, checked] at returned
    | true => rfl
  cases collected : collect (clauses expression) with
  | none => simp [infer, sourceChecked, collected] at returned
  | some alternatives =>
      cases alternatives with
      | nil => simp [infer, sourceChecked, collected] at returned
      | cons first rest =>
          have equal : first :: rest = result := by simpa [infer, sourceChecked, collected] using returned
          rw [← equal]
          simp

theorem infer_inferred_has_typing (algebra : RowFlowSchemes.Algebra Row)
    (rowAntisymm : ∀ {left right}, algebra.le left right → algebra.le right left → left = right)
    (expression : Expr) (result : Principal) (returned : infer expression = .inferred result) :
    ∃ target, Typing (model algebra) [] expression target := by
  have nonempty := infer_inferred_nonempty expression result returned
  cases result with
  | nil => exact False.elim (nonempty rfl)
  | cons first rest =>
      let target := first.scheme.instantiate algebra (fun _ => algebra.empty)
        (fun _ => .bottom) first.output
      exact ⟨target, (infer_inferred_exact algebra rowAntisymm expression (first :: rest) returned target).mp
        ⟨first, List.mem_cons_self, first.instance_of_parameters algebra _ _⟩⟩

/-- Rejection means absence of every original value/row result, throughout
the independently checked supported fragment. -/
theorem infer_rejected_iff (algebra : RowFlowSchemes.Algebra Row)
    (rowAntisymm : ∀ {left right}, algebra.le left right → algebra.le right left → left = right)
    (expression : Expr) :
    (infer expression).status = .rejected ↔ supported expression = true ∧
      ¬ ∃ target, Typing (model algebra) [] expression target := by
  cases returned : infer expression with
  | unsupported =>
      have absent := (infer_unsupported_iff expression).mp (by rw [returned]; rfl)
      simp [Result.status, absent]
  | rejected =>
      have checked : supported expression = true := by
        cases accepted : supported expression with
        | false =>
            have impossible := (infer_unsupported_iff expression).mpr accepted
            simp [returned, Result.status] at impossible
        | true => rfl
      exact ⟨fun _ => ⟨checked, infer_rejected_sound algebra rowAntisymm expression returned⟩, fun _ => rfl⟩
  | inferred result =>
      have witness := infer_inferred_has_typing algebra rowAntisymm expression result returned
      simp [Result.status, witness]

/-- The all-instance theorem also refers directly to the original principal
formula, including its original existentials and value-let alternatives. -/
theorem infer_principal_formula_exact (algebra : RowFlowSchemes.Algebra Row)
    (rowAntisymm : ∀ {left right}, algebra.le left right → algebra.le right left → left = right)
    (expression : Expr) (checked : supported expression = true) (target : Comp (model algebra)) :
    (infer expression).Instance algebra target ↔
      (principal ([] : SchemeEnv Empty) expression).Holds (model algebra) (extend Empty.elim target) :=
  (infer_instances_exact algebra rowAntisymm expression checked target).trans
    (principal_exact (model algebra) expression ([] : SchemeEnv Empty) [] Empty.elim
      (by intro index value; simp [SchemeLookup, BindingLookup]) target).symm

/-- Every expression in the record-construction-free core is supported.
This is proved through the original generator and both value-let branches,
not assumed as a property of an already successful inference run. -/
theorem recordFree_supported (expression : Expr) (core : SourceConstraintSupport.RecordFree expression) :
    supported expression = true := by
  apply Bool.and_eq_true_iff.mpr
  refine ⟨SourceConstraintSupport.recordFree_requiredFieldsOnly expression core, ?_⟩
  apply List.all_eq_true.mpr
  intro clause member
  obtain ⟨compiled, found, rowsSupported⟩ :=
    SourceConstraintSupport.closed_compiler_and_rows_supported expression core clause member
  apply joint_supported_of_status
  intro unsupported
  cases rows : NestedRowRequirements.solveRows compiled.graph compiled.constraints
      (ConstraintProblems.split clause.pack).rows with
  | unsupported => exact rowsSupported rows
  | rejected =>
      simp [JointConstraintInference.infer, found, rows, JointConstraintInference.Result.status] at unsupported
  | solved cache rowScheme =>
      simp [JointConstraintInference.infer, found, rows, JointConstraintInference.Result.status] at unsupported

theorem recordFree_ne_unsupported (expression : Expr)
    (core : SourceConstraintSupport.RecordFree expression) :
    (infer expression).status ≠ .unsupported := by
  intro unsupported
  have failed := (infer_unsupported_iff expression).mp unsupported
  rw [recordFree_supported expression core] at failed
  cases failed

/-- Complete principal inference for the entire record-construction-free
core: lambda, application, value-restricted let, branches, products,
projections, field selection, variants, literals, and the empty record.
The only input restriction is on source syntax; no solver success, support
check result, or model existence is supplied. -/
theorem recordFree_instances_exact (algebra : RowFlowSchemes.Algebra Row)
    (rowAntisymm : ∀ {left right}, algebra.le left right → algebra.le right left → left = right)
    (expression : Expr) (core : SourceConstraintSupport.RecordFree expression)
    (target : Comp (model algebra)) :
    (infer expression).Instance algebra target ↔ Typing (model algebra) [] expression target :=
  infer_instances_exact algebra rowAntisymm expression (recordFree_supported expression core) target

theorem recordFree_rejected_iff (algebra : RowFlowSchemes.Algebra Row)
    (rowAntisymm : ∀ {left right}, algebra.le left right → algebra.le right left → left = right)
    (expression : Expr) (core : SourceConstraintSupport.RecordFree expression) :
    (infer expression).status = .rejected ↔
      ¬ ∃ target, Typing (model algebra) [] expression target := by
  simpa only [recordFree_supported expression core, true_and] using
    infer_rejected_iff algebra rowAntisymm expression

theorem recordFree_principal_formula_exact (algebra : RowFlowSchemes.Algebra Row)
    (rowAntisymm : ∀ {left right}, algebra.le left right → algebra.le right left → left = right)
    (expression : Expr) (core : SourceConstraintSupport.RecordFree expression)
    (target : Comp (model algebra)) :
    (infer expression).Instance algebra target ↔
      (principal ([] : SchemeEnv Empty) expression).Holds (model algebra) (extend Empty.elim target) :=
  infer_principal_formula_exact algebra rowAntisymm expression (recordFree_supported expression core) target

end Yulang.SourcePrincipalInference
