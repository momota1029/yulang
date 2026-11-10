import Yulang.CommonRoleStructuralAssociatedTemplates

/-!
# Checked finite associated source programs

Scope, declared arity, and associated-name membership are computed from raw
obligations. The existing total role registry and scope-resolved source names
remain inputs. This checker recognizes the one-placeholder structural fragment;
its failure is not a new language rejection rule or parser adequacy theorem.
-/
namespace Yulang.CommonRoleCheckedAssociatedPrograms
open Roles
open CommonRoleStructuralAssociatedTemplates (Template Occurrence Program Materializes Derives)
open CommonRoleSettledConstraints (State)
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All)

structure RawOccurrence where
  receiver : Nat
  output : Nat
  name : Nat
  goal : Goal
  deriving DecidableEq, Repr

abbrev RawProgram := List RawOccurrence

def erase (q : Occurrence) : RawOccurrence :=
  ⟨q.receiver, q.output, q.name, q.template.goal⟩

def eraseProgram (p : Program) : RawProgram := p.map erase

/-- Declaration membership, arity and fragment scope, without resolver output. -/
def Valid (roles : RoleDecls) (r : RawOccurrence) : Prop :=
  argsBound r.goal.args ≤ 1 ∧ r.goal.args.length = (roles r.goal.role).arity ∧
    ((roles r.goal.role).assoc r.name).isSome = true

instance (roles : RoleDecls) (r : RawOccurrence) : Decidable (Valid roles r) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def ValidProgram (roles : RoleDecls) (raw : RawProgram) : Prop :=
  ∀ r ∈ raw, Valid roles r

instance (roles : RoleDecls) (raw : RawProgram) : Decidable (ValidProgram roles raw) :=
  inferInstanceAs (Decidable (∀ r ∈ raw, Valid roles r))

def ofValid (roles : RoleDecls) (r : RawOccurrence) (valid : Valid roles r) : Occurrence :=
  ⟨r.receiver, r.output, r.name, ⟨r.goal, valid.1⟩⟩

theorem erase_ofValid (roles : RoleDecls) (r : RawOccurrence) (valid : Valid roles r) :
    erase (ofValid roles r valid) = r := by cases r; rfl

theorem erase_injective : Function.Injective erase := by
  intro a b same
  cases a with
  | mk ar ao an atemplate =>
    cases b with
    | mk br bo bn bt =>
      cases atemplate with
      | mk ag ap =>
        cases bt with
        | mk bg bp =>
          simp only [erase, RawOccurrence.mk.injEq] at same
          rcases same with ⟨rfl, rfl, rfl, rfl⟩
          rfl

theorem eraseProgram_injective : Function.Injective eraseProgram := by
  intro a
  induction a with
  | nil => intro b same; cases b <;> simp_all [eraseProgram]
  | cons a rest ih =>
    intro b same
    cases b with
    | nil => simp [eraseProgram] at same
    | cons b tail =>
      have both : erase a = erase b ∧ eraseProgram rest = eraseProgram tail := by
        simpa [eraseProgram] using same
      rw [erase_injective both.1, ih both.2]

/-- The proof is computed by the checker; callers do not supply it. -/
def build (roles : RoleDecls) : (raw : RawProgram) → ValidProgram roles raw → Program
  | [], _ => []
  | r :: rest, valid => ofValid roles r (valid r (by simp)) ::
      build roles rest (fun q member => valid q (by simp [member]))

theorem erase_build (roles : RoleDecls) (raw : RawProgram) (valid : ValidProgram roles raw) :
    eraseProgram (build roles raw valid) = raw := by
  induction raw with
  | nil => rfl
  | cons r rest ih =>
    simp only [build, eraseProgram, List.map_cons, erase_ofValid]
    exact congrArg (List.cons r) (ih _)

def check (roles : RoleDecls) (raw : RawProgram) : Option Program :=
  if valid : ValidProgram roles raw then some (build roles raw valid) else none

/-- Successful checking preserves every input occurrence exactly, in order. -/
theorem check_exact (roles : RoleDecls) (raw : RawProgram) (p : Program) :
    check roles raw = some p ↔ eraseProgram p = raw ∧ ValidProgram roles raw := by
  unfold check
  split
  · rename_i valid
    constructor
    · intro same
      cases Option.some.inj same
      exact ⟨erase_build roles raw valid, valid⟩
    · intro h
      apply congrArg some
      exact eraseProgram_injective ((erase_build roles raw valid).trans h.1.symm)
  · rename_i invalid
    constructor
    · intro h; contradiction
    · intro h; exact False.elim (invalid h.2)

theorem check_accepts (roles : RoleDecls) (raw : RawProgram) :
    (check roles raw).isSome = true ↔ ValidProgram roles raw := by
  simp [check]

theorem check_fails (roles : RoleDecls) (raw : RawProgram) :
    check roles raw = none ↔ ∃ r ∈ raw, ¬ Valid roles r := by
  simp only [check, dite_eq_right_iff, Option.some_ne_none, imp_false]
  simp [ValidProgram]

theorem checked_length (roles : RoleDecls) (raw : RawProgram) (p : Program)
    (checked : check roles raw = some p) : p.length = raw.length := by
  have h := congrArg List.length ((check_exact roles raw p).mp checked).1
  simpa [eraseProgram] using h

theorem checked_rows (roles : RoleDecls) (raw : RawProgram) (p : Program)
    (checked : check roles raw = some p) (q : Occurrence) (member : q ∈ p) :
    Valid roles (erase q) := by
  obtain ⟨same, valid⟩ := (check_exact roles raw p).mp checked
  apply valid (erase q)
  rw [← same]
  exact List.mem_map.mpr ⟨q, member, rfl⟩

/-- Any materialized goal keeps the checked declaration's arity and name. -/
theorem materialized_declared (roles : RoleDecls) (raw : RawProgram) (p : Program)
    (checked : check roles raw = some p) (q : Occurrence) (member : q ∈ p)
    (head : Inference.Base) (g : Goal) (materialized : Materializes q.template head g) :
    g.args.length = (roles g.role).arity ∧
      ((roles g.role).assoc q.name).isSome = true := by
  have valid := checked_rows roles raw p checked q member
  have shape := CommonRoleStructuralAssociatedTemplates.materializes_shape _ _ _ materialized
  rw [shape.1, shape.2]
  exact valid.2

/-- The checked source boundary feeds the actual solver without a success premise. -/
theorem checked_source_exact (env : AssocEnv) (roles : RoleDecls)
    (wf : WellFormed env.cores) (awf : AssocWellFormed env roles)
    (raw : RawProgram) (p : Program) (checked : check roles raw = some p)
    (s : State (CommonRoleStructuralAssociatedTemplates.table p).length)
    (v : Fin (CommonRoleStructuralAssociatedTemplates.table p).length → Comp Common.model) :
    eraseProgram p = raw ∧ ValidProgram roles raw ∧
      (All Common.model v (CommonRoleStructuralAssociatedTemplates.run env roles wf p s).atoms ↔
        All Common.model v s.atoms ∧ ∃ values,
          CommonRoleSourceDescent.Factors (CommonRoleStructuralAssociatedTemplates.table p) v values ∧
          ∀ name head, Derives env roles p s name head →
            Common.Equivalent (values name) (.base head)) :=
  ⟨((check_exact roles raw p).mp checked).1, ((check_exact roles raw p).mp checked).2,
    CommonRoleStructuralAssociatedTemplates.run_source_exact env roles wf awf p s v⟩

/-- Accepted syntax does not assert consistency: that outcome is characterized separately. -/
theorem checked_solver_exact (env : AssocEnv) (roles : RoleDecls)
    (wf : WellFormed env.cores) (awf : AssocWellFormed env roles)
    (raw : RawProgram) (p : Program) (checked : check roles raw = some p)
    (s : State (CommonRoleStructuralAssociatedTemplates.table p).length) :
    eraseProgram p = raw ∧
      (CommonRoleOpenPropagation.consistent
        (CommonRoleStructuralAssociatedTemplates.run env roles wf p s) = true ↔
        ∃ v : Fin (CommonRoleStructuralAssociatedTemplates.table p).length → Comp Common.model,
          All Common.model v s.atoms ∧ ∃ values,
            CommonRoleSourceDescent.Factors (CommonRoleStructuralAssociatedTemplates.table p) v values ∧
            ∀ name head, Derives env roles p s name head →
              Common.Equivalent (values name) (.base head)) :=
  ⟨((check_exact roles raw p).mp checked).1,
    CommonRoleStructuralAssociatedTemplates.solver_source_exact env roles wf awf p s⟩

end Yulang.CommonRoleCheckedAssociatedPrograms
