import Yulang.CommonRoleSourceEnvironmentCongruence
import Yulang.CommonRoleScalarExpressionInputs

/-! Original annotated scalar expressions feed the actual mixed source dictionary
forest. Equality atoms, slots, evidence and recursive children are computed.
Literal/variable/let syntax with explicit scalar annotations is a finite fragment;
unsupported syntax is not a claim of language rejection. Bindings remain closed
expressions with scope-resolved output names, not parser AST lowering. -/
namespace Yulang.CommonRoleExpressionDictionaryForest
open Roles RoleDictionaries
open CommonRoleAssociatedClauseExtraction (Clause)
open CommonRoleScalarExpressionInputs (Binding Bindings Evaluates Valid Seed Meaning)
open CommonRoleNamedOrdinaryInputs (Input OrdinaryModels)
open CommonRoleSourceDictionaryForest (Report Row Entry)
open CommonRoleSourceRoleObligations (raw ValidSource)
open CommonRoleSourceDiagnosticForest (Materializes)

/-- Both bounds come from checked expression typing and its explicit annotation. -/
def ordinary (bindings : Bindings) : Input :=
  bindings.flatMap fun b => [(.var b.name,.base b.annotation),(.base b.annotation,.var b.name)]

def source (clauses : List Clause) (bindings : Bindings) : CommonRoleCheckedMixedSource.Source :=
  ⟨clauses,ordinary bindings⟩

theorem upper_exact (bindings : Bindings) (name : Nat) (head : Inference.Base) :
    (.var name,.base head) ∈ ordinary bindings ↔
      ∃ b ∈ bindings, b.name = name ∧ b.annotation = head := by
  simp only [ordinary,List.mem_flatMap,List.mem_cons,List.not_mem_nil,or_false,
    Prod.mk.injEq,CommonRoleNamedOrdinaryInputs.Term.var.injEq,
    CommonRoleNamedOrdinaryInputs.Term.base.injEq]
  simp only [reduceCtorEq,and_false,or_false]
  constructor
  · rintro ⟨b,hb,hn,hh⟩; exact ⟨b,hb,hn.symm,hh.symm⟩
  · rintro ⟨b,hb,hn,hh⟩; exact ⟨b,hb,hn.symm,hh.symm⟩

theorem lower_exact (bindings : Bindings) (name : Nat) (head : Inference.Base) :
    (.base head,.var name) ∈ ordinary bindings ↔
      ∃ b ∈ bindings, b.name = name ∧ b.annotation = head := by
  simp only [ordinary,List.mem_flatMap,List.mem_cons,List.not_mem_nil,or_false,
    Prod.mk.injEq,CommonRoleNamedOrdinaryInputs.Term.var.injEq,
    CommonRoleNamedOrdinaryInputs.Term.base.injEq]
  simp only [reduceCtorEq,false_and,false_or]
  constructor
  · rintro ⟨b,hb,hh,hn⟩; exact ⟨b,hb,hn.symm,hh.symm⟩
  · rintro ⟨b,hb,hn,hh⟩; exact ⟨b,hb,hh.symm,hn.symm⟩

theorem no_transfer (bindings : Bindings) (a b : Nat) :
    (.var a,.var b) ∉ ordinary bindings := by
  simp [ordinary]

/-- Exact generated constraints for every valuation, including duplicate names. -/
theorem ordinary_models (bindings : Bindings) (values : Nat → Common.Ty) :
    OrdinaryModels (ordinary bindings) values ↔
      ∀ b ∈ bindings, Common.Equivalent (values b.name) (.base b.annotation) := by
  simp only [OrdinaryModels,ordinary,List.mem_flatMap,forall_exists_index,and_imp]
  constructor
  · intro h b hb
    exact ⟨h (.var b.name,.base b.annotation) b hb (by simp),
      h (.base b.annotation,.var b.name) b hb (by simp)⟩
  · intro h q b hb member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact (h b hb).1
    · exact (h b hb).2

/-- All generated ordinary models are exactly original expression/annotation
models. The validation premise is independently equivalent to Evaluates. -/
theorem ordinary_typing_exact (bindings : Bindings) (valid : Valid bindings)
    (values : Nat → Common.Ty) :
    OrdinaryModels (ordinary bindings) values ↔
      ∀ b ∈ bindings, Meaning b.value b.annotation (values b.name) := by
  rw [ordinary_models]
  constructor
  · intro h b hb
    exact (CommonRoleScalarExpressionInputs.meaning_exact
      ((CommonRoleScalarExpressionInputs.infer_exact ..).mp (valid b hb)) _).mpr (h b hb)
  · intro h b hb
    exact (CommonRoleScalarExpressionInputs.meaning_exact
      ((CommonRoleScalarExpressionInputs.infer_exact ..).mp (valid b hb)) _).mp (h b hb)

/-- No externally supplied ordinary seed appears in the independent judgment. -/
theorem derives_exact (env : AssocEnv) (roles : RoleDecls) (clauses : List Clause)
    (bindings : Bindings) (valid : Valid bindings) (name : Nat) (head : Inference.Base) :
    CommonRoleCheckedMixedSource.Derives env roles (source clauses bindings) name head ↔
      CommonRoleScalarExpressionInputs.Derives env roles clauses bindings name head := by
  constructor
  · intro h
    induction h with
    | initial upper lower =>
      obtain ⟨b,hb,hn,hh⟩ := (upper_exact bindings _ _).mp upper
      rw [← hn,← hh]
      exact .initial (.binding b hb ((CommonRoleScalarExpressionInputs.infer_exact ..).mp (valid b hb)))
    | transfer upper lower _ ih => exact False.elim (no_transfer bindings _ _ upper)
    | equation c e hc he _ step ih => exact .equation c e hc he ih step
  · intro h
    induction h with
    | initial seed =>
      cases seed with
      | binding b hb evaluated =>
        exact .initial ((upper_exact bindings _ _).mpr ⟨b,hb,rfl,rfl⟩)
          ((lower_exact bindings _ _).mpr ⟨b,hb,rfl,rfl⟩)
    | equation c e hc he _ step ih => exact .equation c e hc he ih step

/-- Every name is covered, including bindings not mentioned by any role clause. -/
def Models (env : AssocEnv) (roles : RoleDecls) (clauses : List Clause)
    (bindings : Bindings) : Prop :=
  ∃ values : Nat → Common.Ty, ∀ name head,
    CommonRoleScalarExpressionInputs.Derives env roles clauses bindings name head →
      Common.Equivalent (values name) (.base head)

theorem models_exact (env : AssocEnv) (roles : RoleDecls) (clauses : List Clause)
    (bindings : Bindings) (valid : Valid bindings) :
    CommonRoleCheckedMixedSource.Models env roles (source clauses bindings) ↔
      Models env roles clauses bindings := by
  simp only [CommonRoleCheckedMixedSource.Models,Models,derives_exact env roles clauses bindings valid]
  constructor
  · rintro ⟨v,_,h⟩; exact ⟨v,h⟩
  · rintro ⟨v,h⟩
    refine ⟨v,(ordinary_models bindings v).mpr ?_,h⟩
    intro b hb
    exact h b.name b.annotation (.initial (.binding b hb
      ((CommonRoleScalarExpressionInputs.infer_exact ..).mp (valid b hb))))

def AllDischarged (env : AssocEnv) (roles : RoleDecls) (clauses : List Clause)
    (bindings : Bindings) : Prop :=
  ∀ c ∈ clauses, ∃ b,
    CommonRoleScalarExpressionInputs.Derives env roles clauses bindings c.receiver b ∧
      CommonRoleSourceRoleObligations.Discharges env.cores (fun _ => b) c

theorem discharged_exact (env : AssocEnv) (roles : RoleDecls) (clauses : List Clause)
    (bindings : Bindings) (valid : Valid bindings) :
    CommonRoleEvidenceDischarge.AllDischarged env roles (source clauses bindings) ↔
      AllDischarged env roles clauses bindings := by
  change (∀ c ∈ clauses, ∃ b,
    CommonRoleCheckedMixedSource.Derives env roles (source clauses bindings) c.receiver b ∧
      CommonRoleSourceRoleObligations.Discharges env.cores (fun _ => b) c) ↔ _
  simp only [AllDischarged,derives_exact env roles clauses bindings valid]

def run (env : AssocEnv) (roles : RoleDecls) (wf : WellFormed env.cores)
    (clauses : List Clause) (bindings : Bindings) : Option Report :=
  if Valid bindings then CommonRoleSourceDictionaryForest.run env roles wf (source clauses bindings)
  else none

/-- Independent expression validation and clause scope are the only conditions
for obtaining diagnostics, not consistency or existence of any dictionary. -/
theorem run_exists_iff (env : AssocEnv) (roles : RoleDecls) (wf : WellFormed env.cores)
    (clauses : List Clause) (bindings : Bindings) :
    (∃ r, run env roles wf clauses bindings = some r) ↔
      (∀ b ∈ bindings, Evaluates [] b.value b.annotation) ∧ ValidSource roles clauses := by
  rw [← CommonRoleScalarExpressionInputs.valid_exact]
  by_cases valid : Valid bindings
  · rw [run,ite_eq_left valid,CommonRoleSourceDictionaryForest.run_exists_iff]
    simp only [valid,true_and,source]
  · simp [run,valid]

/-- Soundness and completeness of the public expression-to-dictionary fragment.
Neither ordinary input nor scalar head map is a caller parameter. -/
theorem run_success_iff (env : AssocEnv) (roles : RoleDecls) (wf : WellFormed env.cores)
    (awf : AssocWellFormed env roles) (clauses : List Clause) (bindings : Bindings) :
    (run env roles wf clauses bindings).map Report.observation = some (true,true) ↔
      (∀ b ∈ bindings, Evaluates [] b.value b.annotation) ∧ ValidSource roles clauses ∧
        Models env roles clauses bindings ∧ AllDischarged env roles clauses bindings := by
  rw [← CommonRoleScalarExpressionInputs.valid_exact]
  by_cases valid : Valid bindings
  · rw [run,ite_eq_left valid,CommonRoleSourceDictionaryForest.run_success_iff env roles wf awf,
      models_exact env roles clauses bindings valid,discharged_exact env roles clauses bindings valid]
    simp only [valid,true_and,source]
  · simp [run,valid]

/-- Every actual expression-backed Plan is exactly an independent typed
Dictionary, with the full payload and the originating source clause retained. -/
theorem run_plan_exact (env : AssocEnv) (roles : RoleDecls) (wf : WellFormed env.cores)
    (awf : AssocWellFormed env roles) (clauses : List Clause) (bindings : Bindings)
    (r : Report) (computed : run env roles wf clauses bindings = some r)
    (row : Row) (member : row ∈ r.rows) (c : Clause) (same : row.obligation = raw c)
    (b : Inference.Base) (p : Plan) :
    (∃ t, Entry.mk (.materialized b t) (some p) ∈ row.attempts) ↔
      CommonRoleScalarExpressionInputs.Derives env roles clauses bindings c.receiver b ∧
        ∃ g, Materializes c b g ∧ ∃ d : Dictionary env.cores g, d.erase = p := by
  by_cases valid : Valid bindings
  · rw [run,ite_eq_left valid] at computed
    rw [CommonRoleSourceDictionaryForest.run_plan_exact env roles wf awf _ r computed row member c same b p,
      derives_exact env roles clauses bindings valid]
  · simp [run,valid] at computed

end Yulang.CommonRoleExpressionDictionaryForest
