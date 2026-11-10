import Yulang.CommonRoleAssociatedClauseExtraction

/-!
# Lossless finite source role obligations

Every clause retains a role obligation, even without associated equations.
The discharge interface takes an explicit scalar source-head map. It is not
source inference, dynamic child closure or a language-visible classification.
-/
namespace Yulang.CommonRoleSourceRoleObligations
open Roles
open CommonRoleAssociatedClauseExtraction (Clause Source Equation lower row)
open CommonRoleStructuralAssociatedTemplates (Template Program generate Materializes)
open CommonRoleCheckedAssociatedPrograms (eraseProgram)

structure RawObligation where
  receiver : Nat
  goal : Goal
  deriving DecidableEq, Repr

structure Obligation where
  receiver : Nat
  template : Template

def raw (c : Clause) : RawObligation := ⟨c.receiver, c.goal⟩
def erase (o : Obligation) : RawObligation := ⟨o.receiver, o.template.goal⟩

def ValidClause (roles : RoleDecls) (c : Clause) : Prop :=
  argsBound c.goal.args ≤ 1 ∧ c.goal.args.length = (roles c.goal.role).arity ∧
    ∀ e ∈ c.equations, ((roles c.goal.role).assoc e.name).isSome = true

def ValidSource (roles : RoleDecls) (src : Source) : Prop :=
  ∀ c ∈ src, ValidClause roles c

instance (roles : RoleDecls) (c : Clause) : Decidable (ValidClause roles c) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))
instance (roles : RoleDecls) (src : Source) : Decidable (ValidSource roles src) :=
  inferInstanceAs (Decidable (∀ c ∈ src, ValidClause roles c))

theorem valid_equations (roles : RoleDecls) (src : Source)
    (valid : ValidSource roles src) :
    CommonRoleCheckedAssociatedPrograms.ValidProgram roles (lower src) := by
  apply (CommonRoleAssociatedClauseExtraction.valid_exact roles src).mpr
  intro c hc e he
  exact ⟨(valid c hc).1, (valid c hc).2.1, (valid c hc).2.2 e he⟩

def buildObligations (roles : RoleDecls) :
    (src : Source) → ValidSource roles src → List Obligation
  | [], _ => []
  | c :: rest, valid => ⟨c.receiver, ⟨c.goal, (valid c (by simp)).1⟩⟩ ::
      buildObligations roles rest (fun q h => valid q (by simp [h]))

theorem erase_build (roles : RoleDecls) (src : Source) (valid : ValidSource roles src) :
    (buildObligations roles src valid).map erase = src.map raw := by
  induction src with
  | nil => rfl
  | cons c rest ih =>
    simp only [buildObligations, List.map_cons]
    exact congrArg (List.cons (raw c)) (ih _)

theorem erase_injective : Function.Injective erase := by
  intro a b h
  cases a with
  | mk ar atemplate => cases b with
    | mk br bt => cases atemplate with
      | mk ag ap => cases bt with
        | mk bg bp =>
          simp only [erase, RawObligation.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          rfl

theorem eraseList_injective : Function.Injective (List.map erase) := by
  intro a
  induction a with
  | nil => intro b same; cases b <;> simp_all
  | cons a rest ih =>
    intro b same
    cases b with
    | nil => simp at same
    | cons b tail =>
      have both : erase a = erase b ∧ rest.map erase = tail.map erase := by
        simpa using same
      rw [erase_injective both.1, ih both.2]

structure Package where
  obligations : List Obligation
  equations : Program

def build (roles : RoleDecls) (src : Source) (valid : ValidSource roles src) : Package :=
  ⟨buildObligations roles src valid,
    CommonRoleCheckedAssociatedPrograms.build roles (lower src) (valid_equations roles src valid)⟩

def check (roles : RoleDecls) (src : Source) : Option Package :=
  if valid : ValidSource roles src then some (build roles src valid) else none

/-- Exact erasure preserves one role per clause, not one role per equation. -/
theorem check_exact (roles : RoleDecls) (src : Source) (p : Package) :
    check roles src = some p ↔
      p.obligations.map erase = src.map raw ∧ eraseProgram p.equations = lower src ∧
        ValidSource roles src := by
  unfold check
  split
  · rename_i valid
    constructor
    · intro h
      cases Option.some.inj h
      exact ⟨erase_build roles src valid,
        CommonRoleCheckedAssociatedPrograms.erase_build roles (lower src) _, valid⟩
    · rintro ⟨hrole, heq, _⟩
      apply congrArg some
      have hr := eraseList_injective ((erase_build roles src valid).trans hrole.symm)
      have he := CommonRoleCheckedAssociatedPrograms.eraseProgram_injective
        ((CommonRoleCheckedAssociatedPrograms.erase_build roles (lower src)
          (valid_equations roles src valid)).trans heq.symm)
      cases p
      simp only [build, Package.mk.injEq]
      exact ⟨hr, he⟩
  · rename_i invalid
    constructor
    · intro h; contradiction
    · intro h; exact False.elim (invalid h.2.2)

theorem check_accepts (roles : RoleDecls) (src : Source) :
    (check roles src).isSome = true ↔ ValidSource roles src := by simp [check]

theorem check_fails (roles : RoleDecls) (src : Source) :
    check roles src = none ↔ ∃ c ∈ src, ¬ ValidClause roles c := by
  simp only [check, dite_eq_right_iff, Option.some_ne_none, imp_false]
  simp [ValidSource]

theorem checked_equations (roles : RoleDecls) (src : Source) (p : Package)
    (checked : check roles src = some p) :
    CommonRoleAssociatedClauseExtraction.check roles src = some p.equations := by
  apply (CommonRoleAssociatedClauseExtraction.check_exact roles src p.equations).mpr
  have h := (check_exact roles src p).mp checked
  exact ⟨h.2.1, (CommonRoleAssociatedClauseExtraction.valid_exact roles src).mp
    (valid_equations roles src h.2.2)⟩

theorem checked_count (roles : RoleDecls) (src : Source) (p : Package)
    (checked : check roles src = some p) : p.obligations.length = src.length := by
  have h := congrArg List.length ((check_exact roles src p).mp checked).1
  simpa using h

theorem checked_occurs (roles : RoleDecls) (src : Source) (p : Package)
    (checked : check roles src = some p) (r : RawObligation) :
    (∃ o ∈ p.obligations, erase o = r) ↔ ∃ c ∈ src, raw c = r := by
  rw [← List.mem_map, ← List.mem_map, ((check_exact roles src p).mp checked).1]

/-- Independent source meaning reads structural filling and declarative resolution. -/
def Discharges (impls : List Impl) (heads : Nat → Inference.Base) (c : Clause) : Prop :=
  ∃ payload g, CommonRoleOrdinaryKnownness.encode (heads c.receiver) = some payload ∧
    g.role = c.goal.role ∧ CommonRoleStructuralAssociatedTemplates.Fills payload c.goal.args g.args ∧
      RoleConstraints.Resolves impls g

def runOne (impls : List Impl) (wf : WellFormed impls)
    (heads : Nat → Inference.Base) (o : Obligation) : Bool :=
  decide (argsBound (generate o.template (heads o.receiver)).args = 0) &&
    decide (Roles.resolve impls wf (generate o.template (heads o.receiver)) = .resolved)

theorem run_one_exact (impls : List Impl) (wf : WellFormed impls)
    (heads : Nat → Inference.Base) (o : Obligation) (c : Clause) (same : erase o = raw c) :
    runOne impls wf heads o = true ↔ Discharges impls heads c := by
  have receiver : o.receiver = c.receiver := congrArg RawObligation.receiver same
  have goal : o.template.goal = c.goal := congrArg RawObligation.goal same
  have material : (∃ g, Materializes o.template (heads o.receiver) g ∧
      RoleConstraints.Resolves impls g) ↔ Discharges impls heads c := by
    simp only [Materializes, Discharges, receiver, goal]
    constructor
    · rintro ⟨g, ⟨payload, encoded, role, fills⟩, resolves⟩
      exact ⟨payload, g, encoded, role, fills, resolves⟩
    · rintro ⟨payload, g, encoded, role, fills, resolves⟩
      exact ⟨g, ⟨payload, encoded, role, fills⟩, resolves⟩
  rw [← material]
  simp only [runOne, Bool.and_eq_true, decide_eq_true_eq, RoleConstraints.resolve_exact,
    CommonRoleStructuralAssociatedTemplates.materializes_exact]
  constructor
  · rintro ⟨closed, resolved⟩
    exact ⟨_, ⟨closed, rfl⟩, resolved⟩
  · rintro ⟨g, ⟨closed, rfl⟩, resolved⟩
    exact ⟨closed, resolved⟩

def runRoles (impls : List Impl) (wf : WellFormed impls)
    (heads : Nat → Inference.Base) (p : Package) : Bool :=
  p.obligations.all (runOne impls wf heads)

/-- No associated equation or successful propagation is needed to retain a role. -/
theorem run_roles_exact (impls : List Impl) (wf : WellFormed impls)
    (roles : RoleDecls) (src : Source) (p : Package) (checked : check roles src = some p)
    (heads : Nat → Inference.Base) :
    runRoles impls wf heads p = true ↔ ∀ c ∈ src, Discharges impls heads c := by
  simp only [runRoles, List.all_eq_true]
  constructor
  · intro h c hc
    obtain ⟨o, ho, same⟩ := (checked_occurs roles src p checked (raw c)).mpr ⟨c, hc, rfl⟩
    exact (run_one_exact impls wf heads o c same).mp (h o ho)
  · intro h o ho
    obtain ⟨c, hc, same⟩ := (checked_occurs roles src p checked (erase o)).mp ⟨o, ho, rfl⟩
    exact (run_one_exact impls wf heads o c same.symm).mpr (h c hc)

/-- A missing bare obligation cannot disappear through equation projection. -/
theorem missing_role_blocks (impls : List Impl) (wf : WellFormed impls)
    (roles : RoleDecls) (src : Source) (p : Package) (checked : check roles src = some p)
    (heads : Nat → Inference.Base) (c : Clause) (member : c ∈ src)
    (missing : ¬ Discharges impls heads c) : runRoles impls wf heads p = false := by
  cases h : runRoles impls wf heads p with
  | false => rfl
  | true => exact False.elim (missing ((run_roles_exact impls wf roles src p checked heads).mp h c member))

/-- Public finite-source entry: validation and role execution are both computed. -/
def runSource (impls : List Impl) (wf : WellFormed impls)
    (roles : RoleDecls) (src : Source) (heads : Nat → Inference.Base) : Bool :=
  match check roles src with
  | none => false
  | some p => runRoles impls wf heads p

/-- Unconditional iff for this finite scalar fragment, not whole-language B4. -/
theorem run_source_exact (impls : List Impl) (wf : WellFormed impls)
    (roles : RoleDecls) (src : Source) (heads : Nat → Inference.Base) :
    runSource impls wf roles src heads = true ↔
      ValidSource roles src ∧ ∀ c ∈ src, Discharges impls heads c := by
  unfold runSource
  cases checked : check roles src with
  | none =>
    simp only [Bool.false_eq_true, false_iff, not_and]
    intro valid
    have accepted := (check_accepts roles src).mpr valid
    simp [checked] at accepted
  | some p =>
    rw [run_roles_exact impls wf roles src p checked heads]
    exact (and_iff_right ((check_exact roles src p).mp checked).2.2).symm

/-- Source sibling order is irrelevant to conjunction, including bare clauses. -/
theorem run_source_permutation (impls : List Impl) (wf : WellFormed impls)
    (roles : RoleDecls) (src other : Source) (perm : src.Perm other)
    (heads : Nat → Inference.Base) :
    runSource impls wf roles src heads = runSource impls wf roles other heads := by
  have exactness : runSource impls wf roles src heads = true ↔
      runSource impls wf roles other heads = true := by
    rw [run_source_exact, run_source_exact]
    simp only [ValidSource, perm.mem_iff]
  cases left : runSource impls wf roles src heads <;>
    cases right : runSource impls wf roles other heads <;> simp_all

end Yulang.CommonRoleSourceRoleObligations
