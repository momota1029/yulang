import Yulang.CommonRoleNamedOrdinaryInputs
import Yulang.CommonRoleSourceRoleObligations

/-! One checked boundary for grouped associated clauses and named ordinary input.
The checker retains bare role obligations. The Boolean result is ordinary
consistency after explicit-evidence mixed closure, not role discharge. Names and
finite clauses remain scope-resolved inputs; this is not full source inference,
general ordinary entailment, dynamic child closure or B4 classification. -/
namespace Yulang.CommonRoleCheckedMixedSource
open CommonRoleAssociatedClauseExtraction (Clause Equation Step row)
open CommonRoleCheckedAssociatedPrograms (RawOccurrence erase)
open CommonRoleSourceRoleObligations (Package ValidSource)
open CommonRoleNamedOrdinaryInputs (Input OrdinaryModels)
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All)

structure Source where
  clauses : CommonRoleAssociatedClauseExtraction.Source
  ordinary : Input

/-- Source facts do not inspect a successful check or an allocated state. -/
inductive Derives (env : Roles.AssocEnv) (roles : Roles.RoleDecls) (src : Source) :
    Nat → Inference.Base → Prop
  | initial {a b} : (.var a,.base b) ∈ src.ordinary →
      (.base b,.var a) ∈ src.ordinary → Derives env roles src a b
  | transfer {a c b} : (.var a,.var c) ∈ src.ordinary →
      (.var c,.var a) ∈ src.ordinary → Derives env roles src c b →
      Derives env roles src a b
  | equation (c : Clause) (e : Equation) {head result} :
      c ∈ src.clauses → e ∈ c.equations → Derives env roles src c.receiver head →
      Step env roles c e head result → Derives env roles src e.output result

def Models (env : Roles.AssocEnv) (roles : Roles.RoleDecls) (src : Source) : Prop :=
  ∃ values : Nat → Common.Ty, OrdinaryModels src.ordinary values ∧
    ∀ a b, Derives env roles src a b → Common.Equivalent (values a) (.base b)

def check (roles : Roles.RoleDecls) (src : Source) : Option Package :=
  CommonRoleSourceRoleObligations.check roles src.clauses

theorem checked_derives_exact (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (src : Source) (p : Package) (checked : check roles src = some p)
    (a : Nat) (b : Inference.Base) :
    CommonRoleNamedOrdinaryInputs.Derives env roles p.equations src.ordinary a b ↔
      Derives env roles src a b := by
  have eqcheck := CommonRoleSourceRoleObligations.checked_equations roles src.clauses p checked
  constructor
  · intro h
    induction h with
    | initial upper lower => exact .initial upper lower
    | transfer forward backward _ ih => exact .transfer forward backward ih
    | @associated q head result member _ step ih =>
      have occurs := (CommonRoleAssociatedClauseExtraction.checked_occurs roles
        src.clauses p.equations eqcheck (erase q)).mp ⟨q,member,rfl⟩
      have rawMember := (CommonRoleAssociatedClauseExtraction.lower_exact src.clauses _).mpr occurs
      obtain ⟨c,hc,mapped⟩ := List.mem_flatMap.mp rawMember
      obtain ⟨e,he,reverse⟩ := List.mem_map.mp mapped
      have same := reverse.symm
      have receiver : q.receiver = c.receiver := congrArg RawOccurrence.receiver same
      have output : q.output = e.output := congrArg RawOccurrence.output same
      rw [output]
      exact .equation c e hc he (by simpa only [receiver] using ih)
        ((CommonRoleAssociatedClauseExtraction.step_exact env roles c e q same head result).mp step)
  · intro h
    induction h with
    | initial upper lower => exact .initial upper lower
    | transfer forward backward _ ih => exact .transfer forward backward ih
    | @equation c e head result hc he _ step ih =>
      obtain ⟨q,member,same⟩ := (CommonRoleAssociatedClauseExtraction.checked_occurs roles
        src.clauses p.equations eqcheck (row c e)).mpr (.equation c e hc he)
      have receiver : q.receiver = c.receiver := congrArg RawOccurrence.receiver same
      have output : q.output = e.output := congrArg RawOccurrence.output same
      rw [← output]
      exact .associated q member (by simpa only [receiver] using ih)
        ((CommonRoleAssociatedClauseExtraction.step_exact env roles c e q same head result).mpr step)

abbrev table (src : Source) (p : Package) :=
  CommonRoleNamedOrdinaryInputs.table p.equations src.ordinary
abbrev name (src : Source) (p : Package) :=
  CommonRoleNamedOrdinaryInputs.name p.equations src.ordinary

def finish (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (src : Source) (p : Package) :=
  CommonRoleNamedOrdinaryInputs.run env roles wf p.equations src.ordinary

theorem checked_evidence_exact (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (src : Source) (p : Package) (checked : check roles src = some p)
    (i : Fin (table src p).length) (b : Inference.Base) :
    CommonRoleOrdinaryKnownness.Evidence (finish env roles wf src p).atoms i b ↔
      Derives env roles src (name src p i) b := by
  rw [finish,CommonRoleNamedOrdinaryInputs.run_evidence_exact env roles wf awf,
    checked_derives_exact env roles src p checked]

theorem checked_source_exact (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (src : Source) (p : Package) (checked : check roles src = some p)
    (v : Fin (table src p).length → Comp Common.model) :
    All Common.model v (finish env roles wf src p).atoms ↔
      ∃ values, CommonRoleSourceDescent.Factors (table src p) v values ∧
        OrdinaryModels src.ordinary values ∧
        ∀ a b, Derives env roles src a b → Common.Equivalent (values a) (.base b) := by
  rw [finish,CommonRoleNamedOrdinaryInputs.run_source_exact env roles wf awf]
  simp only [checked_derives_exact env roles src p checked]

theorem checked_solver_exact (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (src : Source) (p : Package) (checked : check roles src = some p) :
    CommonRoleOpenPropagation.consistent (finish env roles wf src p) = true ↔
      Models env roles src := by
  rw [finish,CommonRoleNamedOrdinaryInputs.solver_source_exact env roles wf awf]
  simp only [CommonRoleNamedOrdinaryInputs.Models,Models,
    checked_derives_exact env roles src p checked]

/-- The original role list is retained, including clauses without equations. -/
theorem checked_roles_retained (roles : Roles.RoleDecls) (src : Source)
    (p : Package) (checked : check roles src = some p) :
    p.obligations.map CommonRoleSourceRoleObligations.erase =
      src.clauses.map CommonRoleSourceRoleObligations.raw :=
  ((CommonRoleSourceRoleObligations.check_exact roles src.clauses p).mp checked).1

/-- None means this finite checker failed. Some true means ordinary consistency,
not that every retained role has been resolved. -/
def run (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (src : Source) : Option Bool :=
  (check roles src).map fun p => CommonRoleOpenPropagation.consistent (finish env roles wf src p)

theorem run_none_iff (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (src : Source) :
    run env roles wf src = none ↔ ¬ ValidSource roles src.clauses := by
  simp [run,check,CommonRoleSourceRoleObligations.check]

/-- Outer exactness has no successful-check, generated-program or state premise. -/
theorem run_true_iff (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (src : Source) :
    run env roles wf src = some true ↔
      ValidSource roles src.clauses ∧ Models env roles src := by
  cases checked : check roles src with
  | none =>
    have invalid : ¬ ValidSource roles src.clauses := by
      have := (CommonRoleSourceRoleObligations.check_accepts roles src.clauses)
      change (check roles src).isSome = true ↔ _ at this
      simp only [checked,Option.isSome_none,Bool.false_eq_true,false_iff] at this
      exact this
    simp [run,checked,invalid]
  | some p =>
    have valid := ((CommonRoleSourceRoleObligations.check_exact roles src.clauses p).mp checked).2.2
    simpa only [run,checked,Option.map_some,Option.some.injEq,valid,true_and] using
      checked_solver_exact env roles wf awf src p checked

theorem run_false_iff (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (src : Source) :
    run env roles wf src = some false ↔
      ValidSource roles src.clauses ∧ ¬ Models env roles src := by
  have ht := run_true_iff env roles wf awf src
  have hn := run_none_iff env roles wf src
  cases h : run env roles wf src with
  | none => simp_all
  | some b => cases b <;> simp_all

/-- Sibling reordering and repetition preserve independent source derivations. -/
theorem derives_congr (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (left right : Source)
    (clauses : ∀ c, c ∈ left.clauses ↔ c ∈ right.clauses)
    (ordinary : ∀ q, q ∈ left.ordinary ↔ q ∈ right.ordinary)
    (a : Nat) (b : Inference.Base) :
    Derives env roles left a b ↔ Derives env roles right a b := by
  have direction (x y : Source)
      (cs : ∀ c ∈ x.clauses, c ∈ y.clauses)
      (os : ∀ q ∈ x.ordinary, q ∈ y.ordinary)
      (a : Nat) (b : Inference.Base) (h : Derives env roles x a b) :
      Derives env roles y a b := by
    induction h with
    | initial up lo => exact .initial (os _ up) (os _ lo)
    | transfer up lo _ ih => exact .transfer (os _ up) (os _ lo) ih
    | equation c e hc he _ step ih => exact .equation c e (cs c hc) he ih step
  exact ⟨direction left right (fun c h => (clauses c).mp h)
      (fun q h => (ordinary q).mp h) a b,
    direction right left (fun c h => (clauses c).mpr h)
      (fun q h => (ordinary q).mpr h) a b⟩

theorem models_congr (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (left right : Source)
    (clauses : ∀ c, c ∈ left.clauses ↔ c ∈ right.clauses)
    (ordinary : ∀ q, q ∈ left.ordinary ↔ q ∈ right.ordinary) :
    Models env roles left ↔ Models env roles right := by
  simp only [Models,OrdinaryModels,ordinary,
    derives_congr env roles left right clauses ordinary]

/-- Reordering/duplicating either source list cannot change the outer outcome,
even though concrete allocation, slots and generated states can change. -/
theorem run_congr (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (left right : Source)
    (clauses : ∀ c, c ∈ left.clauses ↔ c ∈ right.clauses)
    (ordinary : ∀ q, q ∈ left.ordinary ↔ q ∈ right.ordinary) :
    run env roles wf left = run env roles wf right := by
  have valid : ValidSource roles left.clauses ↔ ValidSource roles right.clauses := by
    simp only [ValidSource,clauses]
  have models := models_congr env roles left right clauses ordinary
  cases hl : run env roles wf left with
  | none =>
    have h := (run_none_iff env roles wf left).mp hl
    exact ((run_none_iff env roles wf right).mpr (fun v => h (valid.mpr v))).symm
  | some b => cases b with
    | false =>
      have h := (run_false_iff env roles wf awf left).mp hl
      exact ((run_false_iff env roles wf awf right).mpr
        ⟨valid.mp h.1,fun m => h.2 (models.mpr m)⟩).symm
    | true =>
      have h := (run_true_iff env roles wf awf left).mp hl
      exact ((run_true_iff env roles wf awf right).mpr ⟨valid.mp h.1,models.mp h.2⟩).symm

end Yulang.CommonRoleCheckedMixedSource
