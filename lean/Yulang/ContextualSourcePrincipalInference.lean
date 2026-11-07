import Yulang.SourcePrincipalInference
import Yulang.ContextualJointConstraintInference

/-!
# Principal source inference in the concrete contextual model

The source generator, clause collector, support checker and executable infer
are exactly the existing algorithms. All returned alternatives, captured let
slots and shared row/value parameters are retained. Only the interpretation of
instances changes to the proved contextual producer order.

The all-instance theorem is stated against the independent `Inference.Typing`
judgment in this concrete model. Its support condition is the executable source
syntax check, not inference success. For `RecordFree` the support check is proved
from source syntax: lambda, application, let, branches, pairs, projections,
field access, variants, literals and the old empty record require no successful
solve premise. Record construction is covered when the existing checker accepts;
presence defaults and general open-tail support remain separate obligations.
-/

namespace Yulang.ContextualSourcePrincipalInference

open Inference ConstraintNormalForm

universe u
variable {Row : Type u}

abbrev model := @ContextualJointConstraintInference.model
abbrev Alternative := SourcePrincipalInference.Alternative
abbrev Alternative.ofClause := @SourcePrincipalInference.Alternative.ofClause
abbrev Principal := SourcePrincipalInference.Principal
abbrev Status := SourcePrincipalInference.Status
abbrev Result := SourcePrincipalInference.Result
abbrev Result.status := @SourcePrincipalInference.Result.status
abbrev collect := SourcePrincipalInference.collect
abbrev clauses := SourcePrincipalInference.clauses
abbrev infer := SourcePrincipalInference.infer
abbrev supported := SourcePrincipalInference.supported

def Alternative.Instance (algebra : RowFlowSchemes.Algebra Row)
    (alternative : Alternative) (target : Comp (model algebra)) : Prop :=
  ContextualJointConstraintInference.Scheme.Instance alternative.scheme algebra alternative.output target

def Principal.Instance (algebra : RowFlowSchemes.Algebra Row)
    (principal : Principal) (target : Comp (model algebra)) : Prop :=
  ∃ alternative ∈ principal, Alternative.Instance algebra alternative target

def Result.Instance (algebra : RowFlowSchemes.Algebra Row)
    (target : Comp (model algebra)) : Result → Prop
  | .inferred principal => Principal.Instance algebra principal target
  | _ => False

theorem collect_none_iff (clauses : List (Clause (Option Empty))) :
    collect clauses = none ↔
      ∃ clause ∈ clauses, ContextualJointConstraintInference.supported
        (ConstraintProblems.split clause.pack) = false :=
  SourcePrincipalInference.collect_none_iff clauses

theorem collect_some_supported (clauses : List (Clause (Option Empty))) (result : Principal)
    (returned : collect clauses = some result) :
    ∀ clause ∈ clauses, ContextualJointConstraintInference.supported
      (ConstraintProblems.split clause.pack) = true :=
  SourcePrincipalInference.collect_some_supported clauses result returned

theorem infer_unsupported_iff (expression : Expr) :
    (infer expression).status = .unsupported ↔ supported expression = false :=
  SourcePrincipalInference.infer_unsupported_iff expression

theorem infer_optional_unsupported (expression : Expr)
    (optional : expression.requiredFieldsOnly = false) : infer expression = .unsupported :=
  SourcePrincipalInference.infer_optional_unsupported expression optional

theorem recordFree_supported (expression : Expr) (core : SourceConstraintSupport.RecordFree expression) :
    supported expression = true := SourcePrincipalInference.recordFree_supported expression core

theorem recordFree_ne_unsupported (expression : Expr) (core : SourceConstraintSupport.RecordFree expression) :
    (infer expression).status ≠ .unsupported :=
  SourcePrincipalInference.recordFree_ne_unsupported expression core

/-- Exactness of the computed finite family. Rejected branches contribute
no instances, while every successful branch keeps all its free parameters. -/
theorem collect_instances_exact (algebra : RowFlowSchemes.Algebra Row)
    (rowAntisymm : ∀ {left right}, algebra.le left right → algebra.le right left → left = right)
    (clauses : List (Clause (Option Empty))) (result : Principal)
    (returned : collect clauses = some result) (target : Comp (model algebra)) :
    Principal.Instance algebra result target ↔
      ∃ clause ∈ clauses,
        (ConstraintProblems.split clause.pack).Instance (model algebra) (Fin.last clause.locals) target := by
  induction clauses generalizing result with
  | nil =>
      have equal : result = [] := (Option.some.inj returned).symm
      subst result
      simp [Principal.Instance]
  | cons clause rest ih =>
      have checked := collect_some_supported (clause :: rest) result returned clause List.mem_cons_self
      have exactHead := ContextualJointConstraintInference.infer_instances_exact algebra rowAntisymm
        (ConstraintProblems.split clause.pack) checked (Fin.last clause.locals) target
      cases solved : ContextualJointConstraintInference.infer (ConstraintProblems.split clause.pack) with
      | unsupported => simp [collect, SourcePrincipalInference.collect, solved] at returned
      | rejected =>
          have tail : collect rest = some result := by simpa only [collect, SourcePrincipalInference.collect, solved] using returned
          have absent : ¬ (ConstraintProblems.split clause.pack).Instance (model algebra)
              (Fin.last clause.locals) target := by
            intro accepted
            have impossible := exactHead.mp accepted
            simp [solved, ContextualJointConstraintInference.Result.Instance] at impossible
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
          | none => simp [collect, SourcePrincipalInference.collect, solved, tail] at returned
          | some alternatives =>
              have equal : result = Alternative.ofClause clause scheme :: alternatives :=
                (Option.some.inj (by simpa [collect, SourcePrincipalInference.collect, solved, tail] using returned)).symm
              subst result
              have headExact : Alternative.Instance algebra (Alternative.ofClause clause scheme) target ↔
                  (ConstraintProblems.split clause.pack).Instance (model algebra)
                    (Fin.last clause.locals) target := by
                simpa [solved, ContextualJointConstraintInference.Result.Instance,
                  Alternative.Instance, Alternative.ofClause, SourcePrincipalInference.Alternative.ofClause] using exactHead.symm
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

/-- All instances of the actual inference result are exactly the original
declarative typings, provided only the executable support check succeeds. -/
theorem infer_instances_exact (algebra : RowFlowSchemes.Algebra Row)
    (rowAntisymm : ∀ {left right}, algebra.le left right → algebra.le right left → left = right)
    (expression : Expr) (checked : supported expression = true) (target : Comp (model algebra)) :
    Result.Instance algebra target (infer expression) ↔ Typing (model algebra) [] expression target := by
  have sourceChecked := (Bool.and_eq_true_iff.mp checked).1
  rw [ConstraintProblems.closed_source_problems_exact (model algebra)
    (ProducerContextualRegular.producerLe_refl) ProducerContextualRegular.producerLe_trans
    algebra.refl algebra.trans expression target]
  change Result.Instance algebra target (infer expression) ↔
    ∃ clause ∈ clauses expression,
      (ConstraintProblems.split clause.pack).Instance (model algebra) (Fin.last clause.locals) target
  cases returned : collect (clauses expression) with
  | none =>
      have failed := (infer_unsupported_iff expression).mp
        (by simp [infer, SourcePrincipalInference.infer, sourceChecked, returned, SourcePrincipalInference.Result.status])
      rw [checked] at failed
      cases failed
  | some result =>
      have exact := collect_instances_exact algebra rowAntisymm (clauses expression) result returned target
      cases result with
      | nil => simpa only [infer, SourcePrincipalInference.infer, sourceChecked, ↓reduceIte, returned, Result.Instance, Principal.Instance,
          List.not_mem_nil, false_and, exists_false] using exact
      | cons first rest => simpa only [infer, SourcePrincipalInference.infer, sourceChecked, ↓reduceIte, returned, Result.Instance] using exact

/-- A returned principal family represents every original result type and
row. The only operational premise names the actual computed return value. -/
theorem infer_inferred_exact (algebra : RowFlowSchemes.Algebra Row)
    (rowAntisymm : ∀ {left right}, algebra.le left right → algebra.le right left → left = right)
    (expression : Expr) (result : Principal) (returned : infer expression = .inferred result)
    (target : Comp (model algebra)) :
    Principal.Instance algebra result target ↔ Typing (model algebra) [] expression target := by
  have checked : supported expression = true := by
    cases accepted : supported expression with
    | false =>
        have failed := (infer_unsupported_iff expression).mpr accepted
        simp [returned, SourcePrincipalInference.Result.status] at failed
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
        simp [returned, SourcePrincipalInference.Result.status] at failed
    | true => rfl
  rintro ⟨target, typed⟩
  have accepted := (infer_instances_exact algebra rowAntisymm expression checked target).mpr typed
  simp [returned, Result.Instance] at accepted

theorem Alternative.instance_of_parameters (algebra : RowFlowSchemes.Algebra Row)
    (alternative : Alternative) (rowParameter : Fin alternative.slots → Row)
    (valueParameter : Fin alternative.scheme.size → ContextualJointConstraintInference.Value Row) :
    Alternative.Instance algebra alternative
      (alternative.scheme.instantiate algebra rowParameter valueParameter alternative.output) :=
  ⟨rowParameter, valueParameter, ProducerContextualRegular.producerLe_refl _, algebra.refl _⟩

theorem infer_inferred_nonempty (expression : Expr) (result : Principal)
    (returned : infer expression = .inferred result) : result ≠ [] :=
  SourcePrincipalInference.infer_inferred_nonempty expression result returned

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
        ⟨first, List.mem_cons_self, Alternative.instance_of_parameters algebra first _ _⟩⟩

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
      simp [SourcePrincipalInference.Result.status, absent]
  | rejected =>
      have checked : supported expression = true := by
        cases accepted : supported expression with
        | false =>
            have impossible := (infer_unsupported_iff expression).mpr accepted
            simp [returned, SourcePrincipalInference.Result.status] at impossible
        | true => rfl
      exact ⟨fun _ => ⟨checked, infer_rejected_sound algebra rowAntisymm expression returned⟩, fun _ => rfl⟩
  | inferred result =>
      have witness := infer_inferred_has_typing algebra rowAntisymm expression result returned
      simp [SourcePrincipalInference.Result.status, witness]

/-- The all-instance theorem also refers directly to the original principal
formula, including its original existentials and value-let alternatives. -/
theorem infer_principal_formula_exact (algebra : RowFlowSchemes.Algebra Row)
    (rowAntisymm : ∀ {left right}, algebra.le left right → algebra.le right left → left = right)
    (expression : Expr) (checked : supported expression = true) (target : Comp (model algebra)) :
    Result.Instance algebra target (infer expression) ↔
      (principal ([] : SchemeEnv Empty) expression).Holds (model algebra) (extend Empty.elim target) :=
  (infer_instances_exact algebra rowAntisymm expression checked target).trans
    (principal_exact (model algebra) expression ([] : SchemeEnv Empty) [] Empty.elim
      (by intro index value; simp [SchemeLookup, BindingLookup]) target).symm

/-- Complete principal inference for the entire record-construction-free
core: lambda, application, value-restricted let, branches, products,
projections, field selection, variants, literals, and the empty record.
The only input restriction is on source syntax; no solver success, support
check result, or model existence is supplied. -/
theorem recordFree_instances_exact (algebra : RowFlowSchemes.Algebra Row)
    (rowAntisymm : ∀ {left right}, algebra.le left right → algebra.le right left → left = right)
    (expression : Expr) (core : SourceConstraintSupport.RecordFree expression)
    (target : Comp (model algebra)) :
    Result.Instance algebra target (infer expression) ↔ Typing (model algebra) [] expression target :=
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
    Result.Instance algebra target (infer expression) ↔
      (principal ([] : SchemeEnv Empty) expression).Holds (model algebra) (extend Empty.elim target) :=
  infer_principal_formula_exact algebra rowAntisymm expression (recordFree_supported expression core) target


end Yulang.ContextualSourcePrincipalInference
