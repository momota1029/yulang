import Yulang.CommonRoleCheckedAssociatedPrograms

/-!
# Exact extraction of grouped associated equations

This finite, scope-resolved syntax carrier projects associated equations only.
Empty equation lists do not discharge bare role obligations. Parser adequacy,
visibility, registry construction and dynamic where generation remain outside.
-/
namespace Yulang.CommonRoleAssociatedClauseExtraction
open Roles
open CommonRoleCheckedAssociatedPrograms (RawOccurrence RawProgram Valid erase eraseProgram)
open CommonRoleStructuralAssociatedTemplates (Program Materializes)
open CommonRoleSettledConstraints (State)
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All)

structure Equation where
  name : Nat
  output : Nat
  deriving DecidableEq, Repr

structure Clause where
  receiver : Nat
  goal : Goal
  equations : List Equation
  deriving DecidableEq, Repr

abbrev Source := List Clause

def row (c : Clause) (e : Equation) : RawOccurrence :=
  ⟨c.receiver, e.output, e.name, c.goal⟩

def lower (src : Source) : RawProgram :=
  src.flatMap fun c => c.equations.map (row c)

/-- Independent source occurrence provenance, before any checker or resolver. -/
inductive Occurs (src : Source) : RawOccurrence → Prop
  | equation (c : Clause) (e : Equation) : c ∈ src → e ∈ c.equations →
      Occurs src (row c e)

theorem lower_exact (src : Source) (r : RawOccurrence) :
    r ∈ lower src ↔ Occurs src r := by
  constructor
  · intro h
    obtain ⟨c, hc, member⟩ := List.mem_flatMap.mp h
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp member
    exact .equation c e hc he
  · intro h
    cases h with
    | equation c e hc he =>
      exact List.mem_flatMap.mpr ⟨c, hc, List.mem_map.mpr ⟨e, he, rfl⟩⟩

/-- List equality retains duplicates and order, unlike membership alone. -/
theorem lower_cons (c : Clause) (src : Source) :
    lower (c :: src) = c.equations.map (row c) ++ lower src := rfl

theorem lower_append (a b : Source) : lower (a ++ b) = lower a ++ lower b := by
  simp [lower]

theorem lower_length (src : Source) :
    (lower src).length = (src.map fun c => c.equations.length).sum := by
  induction src with
  | nil => rfl
  | cons c rest ih => simp [lower_cons, ih]

/-- A concrete source position survives lowering even when adjacent rows are equal. -/
theorem lower_position (before after : Source) (c : Clause)
    (j : Fin c.equations.length) :
    (lower (before ++ c :: after))[(lower before).length + j.val]? =
      some (row c c.equations[j.val]) := by
  rw [lower_append, lower_cons, List.getElem?_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]
  rw [List.getElem?_append_left (by simp)]
  simp

def ValidSource (roles : RoleDecls) (src : Source) : Prop :=
  ∀ c ∈ src, ∀ e ∈ c.equations, Valid roles (row c e)

instance (roles : RoleDecls) (src : Source) : Decidable (ValidSource roles src) :=
  inferInstanceAs (Decidable (∀ c ∈ src, ∀ e ∈ c.equations, Valid roles (row c e)))

theorem valid_exact (roles : RoleDecls) (src : Source) :
    CommonRoleCheckedAssociatedPrograms.ValidProgram roles (lower src) ↔
      ValidSource roles src := by
  constructor
  · intro h c hc e he
    exact h _ ((lower_exact src _).mpr (.equation c e hc he))
  · intro h r hr
    cases (lower_exact src r).mp hr with
    | equation c e hc he => exact h c hc e he

def check (roles : RoleDecls) (src : Source) : Option Program :=
  CommonRoleCheckedAssociatedPrograms.check roles (lower src)

theorem check_exact (roles : RoleDecls) (src : Source) (p : Program) :
    check roles src = some p ↔ eraseProgram p = lower src ∧ ValidSource roles src := by
  rw [check, CommonRoleCheckedAssociatedPrograms.check_exact, valid_exact]

theorem check_accepts (roles : RoleDecls) (src : Source) :
    (check roles src).isSome = true ↔ ValidSource roles src := by
  rw [check, CommonRoleCheckedAssociatedPrograms.check_accepts, valid_exact]

theorem check_fails (roles : RoleDecls) (src : Source) :
    check roles src = none ↔ ∃ c ∈ src, ∃ e ∈ c.equations, ¬ Valid roles (row c e) := by
  rw [check, CommonRoleCheckedAssociatedPrograms.check_fails]
  constructor
  · rintro ⟨r, member, invalid⟩
    cases (lower_exact src r).mp member with
    | equation c e hc he => exact ⟨c, hc, e, he, invalid⟩
  · rintro ⟨c, hc, e, he, invalid⟩
    exact ⟨row c e, (lower_exact src _).mpr (.equation c e hc he), invalid⟩

theorem checked_count (roles : RoleDecls) (src : Source) (p : Program)
    (checked : check roles src = some p) :
    p.length = (src.map fun c => c.equations.length).sum :=
  (CommonRoleCheckedAssociatedPrograms.checked_length roles (lower src) p checked).trans
    (lower_length src)

/-- Every produced row has a source, and every source equation has a produced row. -/
theorem checked_occurs (roles : RoleDecls) (src : Source) (p : Program)
    (checked : check roles src = some p) (r : RawOccurrence) :
    (∃ q ∈ p, erase q = r) ↔ Occurs src r := by
  rw [← lower_exact, ← ((check_exact roles src p).mp checked).1]
  exact List.mem_map.symm

/-- Independent source equation meaning; no executable resolver is inspected. -/
def Step (env : AssocEnv) (roles : RoleDecls) (c : Clause) (e : Equation)
    (head result : Inference.Base) : Prop :=
  ∃ payload g, CommonRoleOrdinaryKnownness.encode head = some payload ∧
    g.role = c.goal.role ∧ CommonRoleStructuralAssociatedTemplates.Fills payload c.goal.args g.args ∧
    RoleConstraints.Resolves env.cores g ∧ ∃ rhs, AssocDerives env roles g e.name rhs ∧
      CommonRoleAssociatedStateFlow.scalar rhs = some result

theorem step_exact (env : AssocEnv) (roles : RoleDecls) (c : Clause) (e : Equation)
    (q : CommonRoleStructuralAssociatedTemplates.Occurrence) (same : erase q = row c e)
    (head result : Inference.Base) :
    CommonRoleStructuralAssociatedTemplates.Step env roles q head result ↔
      Step env roles c e head result := by
  have goal : q.template.goal = c.goal := congrArg RawOccurrence.goal same
  have name : q.name = e.name := congrArg RawOccurrence.name same
  simp only [CommonRoleStructuralAssociatedTemplates.Step, Materializes, Step, goal, name]
  constructor
  · rintro ⟨g, ⟨payload, enc, role, fills⟩, resolves, rhs, derived, scalar⟩
    exact ⟨payload, g, enc, role, fills, resolves, rhs, derived, scalar⟩
  · rintro ⟨payload, g, enc, role, fills, resolves, rhs, derived, scalar⟩
    exact ⟨g, ⟨payload, enc, role, fills⟩, resolves, rhs, derived, scalar⟩

/-- Initial ordinary evidence is read through the computed table of p. Only the
seed interface depends on p; recursive steps inspect source clauses directly. -/
inductive Derives (env : AssocEnv) (roles : RoleDecls) (src : Source)
    (p : Program) (s : State (CommonRoleStructuralAssociatedTemplates.table p).length) :
    Nat → Inference.Base → Prop
  | initial {name head} : CommonRoleNamedAssociatedSourceModels.Seed
      (CommonRoleStructuralAssociatedTemplates.compile p) s name head →
      Derives env roles src p s name head
  | equation (c : Clause) (e : Equation) {head result} : c ∈ src → e ∈ c.equations →
      Derives env roles src p s c.receiver head → Step env roles c e head result →
      Derives env roles src p s e.output result

theorem derives_exact (env : AssocEnv) (roles : RoleDecls) (src : Source)
    (p : Program) (checked : check roles src = some p)
    (s : State (CommonRoleStructuralAssociatedTemplates.table p).length)
    (name : Nat) (head : Inference.Base) :
    CommonRoleStructuralAssociatedTemplates.Derives env roles p s name head ↔
      Derives env roles src p s name head := by
  constructor
  · intro h
    induction h with
    | initial seed => exact .initial seed
    | @associated q head result member _ step ih =>
      have rawMember : erase q ∈ lower src := by
        rw [← ((check_exact roles src p).mp checked).1]
        exact List.mem_map.mpr ⟨q, member, rfl⟩
      obtain ⟨c, hc, mapped⟩ := List.mem_flatMap.mp rawMember
      obtain ⟨e, he, reverse⟩ := List.mem_map.mp mapped
      have same := reverse.symm
      have receiver : q.receiver = c.receiver := congrArg RawOccurrence.receiver same
      have output : q.output = e.output := congrArg RawOccurrence.output same
      rw [output]
      exact .equation c e hc he (by simpa only [receiver] using ih)
        ((step_exact env roles c e q same head result).mp step)
  · intro h
    induction h with
    | initial seed => exact .initial seed
    | @equation c e head result hc he _ step ih =>
      obtain ⟨q, member, same⟩ := (checked_occurs roles src p checked (row c e)).mpr
        (.equation c e hc he)
      have receiver : q.receiver = c.receiver := congrArg RawOccurrence.receiver same
      have output : q.output = e.output := congrArg RawOccurrence.output same
      rw [← output]
      exact .associated q member (by simpa only [receiver] using ih)
        ((step_exact env roles c e q same head result).mpr step)

/-- Actual saturation evidence iff independently derived source-clause evidence. -/
theorem run_evidence_exact (env : AssocEnv) (roles : RoleDecls)
    (wf : WellFormed env.cores) (awf : AssocWellFormed env roles)
    (src : Source) (p : Program) (checked : check roles src = some p)
    (s : State (CommonRoleStructuralAssociatedTemplates.table p).length)
    (slot : Fin (CommonRoleStructuralAssociatedTemplates.table p).length)
    (head : Inference.Base) :
    CommonRoleOrdinaryKnownness.Evidence
      (CommonRoleStructuralAssociatedTemplates.run env roles wf p s).atoms slot head ↔
      Derives env roles src p s
        (CommonRoleSourceIdentity.source (CommonRoleStructuralAssociatedTemplates.table p) slot) head :=
  (CommonRoleStructuralAssociatedTemplates.run_evidence_exact env roles wf awf p s slot head).trans
    (derives_exact env roles src p checked s _ head)

theorem run_source_exact (env : AssocEnv) (roles : RoleDecls)
    (wf : WellFormed env.cores) (awf : AssocWellFormed env roles)
    (src : Source) (p : Program) (checked : check roles src = some p)
    (s : State (CommonRoleStructuralAssociatedTemplates.table p).length)
    (v : Fin (CommonRoleStructuralAssociatedTemplates.table p).length → Comp Common.model) :
    All Common.model v (CommonRoleStructuralAssociatedTemplates.run env roles wf p s).atoms ↔
      All Common.model v s.atoms ∧ ∃ values,
        CommonRoleSourceDescent.Factors (CommonRoleStructuralAssociatedTemplates.table p) v values ∧
          ∀ name head, Derives env roles src p s name head →
            Common.Equivalent (values name) (.base head) := by
  rw [CommonRoleStructuralAssociatedTemplates.run_source_exact env roles wf awf]
  simp only [derives_exact env roles src p checked s]

/-- Solver consistency is separate from syntactic acceptance. -/
theorem solver_source_exact (env : AssocEnv) (roles : RoleDecls)
    (wf : WellFormed env.cores) (awf : AssocWellFormed env roles)
    (src : Source) (p : Program) (checked : check roles src = some p)
    (s : State (CommonRoleStructuralAssociatedTemplates.table p).length) :
    CommonRoleOpenPropagation.consistent
      (CommonRoleStructuralAssociatedTemplates.run env roles wf p s) = true ↔
      ∃ v : Fin (CommonRoleStructuralAssociatedTemplates.table p).length → Comp Common.model,
        All Common.model v s.atoms ∧ ∃ values,
          CommonRoleSourceDescent.Factors (CommonRoleStructuralAssociatedTemplates.table p) v values ∧
            ∀ name head, Derives env roles src p s name head →
              Common.Equivalent (values name) (.base head) := by
  rw [CommonRoleOpenPropagation.consistent_exact]
  exact exists_congr (run_source_exact env roles wf awf src p checked s)

end Yulang.CommonRoleAssociatedClauseExtraction
