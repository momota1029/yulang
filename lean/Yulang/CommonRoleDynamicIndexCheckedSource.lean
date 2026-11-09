import Yulang.CommonRoleDynamicIndexSourceExecution

/-! A checked entrance for the finite named string Index adapter.
Missing endpoints are adapter diagnostics, not language rejection. Scope success
neither constructs an output model nor proves all obligations executable. -/
namespace Yulang.CommonRoleDynamicIndexCheckedSource
open CommonRoleSourceIdentity (Table Slot source)
open CommonRoleSettledConstraints (State)
open CommonRoleDynamicIndexSource (Requests WellScoped Derived)
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All)

def present (table : Table) (name : Nat) : Bool :=
  (List.finRange table.length).any fun i => source table i == name

theorem present_exact (table : Table) (name : Nat) :
    present table name = true ↔ ∃ i : Slot table, source table i = name := by
  simp [present]

def covered (table : Table) (r : Nat × Nat) : Bool :=
  present table r.1 && present table r.2

theorem covered_exact (table : Table) (r : Nat × Nat) :
    covered table r = true ↔ ∃ i j : Slot table, source table i = r.1 ∧ source table j = r.2 := by
  simp only [covered, Bool.and_eq_true, present_exact]
  constructor
  · rintro ⟨⟨i,hi⟩,⟨j,hj⟩⟩; exact ⟨i,j,hi,hj⟩
  · rintro ⟨i,j,hi,hj⟩; exact ⟨⟨i,hi⟩,⟨j,hj⟩⟩

def missing (table : Table) (requests : Requests) : Requests :=
  requests.filter fun r => !covered table r

theorem missing_exact (table : Table) (requests : Requests) (r : Nat × Nat) :
    r ∈ missing table requests ↔ r ∈ requests ∧
      ¬ ∃ i j : Slot table, source table i = r.1 ∧ source table j = r.2 := by
  rw [show (∃ i j : Slot table, source table i = r.1 ∧ source table j = r.2) ↔ covered table r = true from (covered_exact table r).symm]
  simp [missing]

theorem missing_nil_iff (table : Table) (requests : Requests) :
    missing table requests = [] ↔ WellScoped table requests := by
  rw [List.eq_nil_iff_forall_not_mem]
  simp only [missing_exact, WellScoped]
  constructor
  · intro h r hr
    apply Classical.byContradiction
    intro hn
    exact h r ⟨hr,hn⟩
  · intro h r hr
    exact hr.2 (h r hr.1)

def run (table : Table) (s : State table.length) (requests : Requests) :
    Except Requests (State table.length) :=
  if missing table requests = [] then .ok (CommonRoleDynamicIndexSource.output table s requests)
  else .error (missing table requests)

theorem run_ok_iff (table : Table) (s : State table.length) (requests : Requests)
    (out : State table.length) :
    run table s requests = .ok out ↔
      WellScoped table requests ∧ out = CommonRoleDynamicIndexSource.output table s requests := by
  simp only [run]
  split
  · rename_i h
    simp only [Except.ok.injEq]
    exact ⟨fun he => ⟨(missing_nil_iff ..).mp h,he.symm⟩,
      fun he => he.2.symm⟩
  · rename_i h
    constructor
    · intro he; cases he
    · intro he; exact False.elim (h ((missing_nil_iff ..).mpr he.1))

theorem run_error_iff (table : Table) (s : State table.length) (requests errors : Requests) :
    run table s requests = .error errors ↔
      ¬ WellScoped table requests ∧ errors = missing table requests := by
  unfold run
  split
  · rename_i h
    constructor
    · intro he; cases he
    · intro he; exact False.elim (he.1 ((missing_nil_iff ..).mp h))
  · rename_i h
    simp only [Except.error.injEq]
    exact ⟨fun he => ⟨fun hs => h ((missing_nil_iff ..).mpr hs),he.symm⟩,
      fun he => he.2.symm⟩

/-- Every malformed request is reported, not silently compiled away. -/
theorem error_nonempty (table : Table) (s : State table.length) (requests errors : Requests)
    (h : run table s requests = .error errors) : errors ≠ [] := by
  obtain ⟨hs,rfl⟩ := (run_error_iff ..).mp h
  exact fun hn => hs ((missing_nil_iff ..).mp hn)

theorem success_coverage (table : Table) (s : State table.length) (requests : Requests)
    (out : State table.length) (h : run table s requests = .ok out)
    (r : Nat × Nat) (hr : r ∈ requests) :
    ∃ i j : Slot table, source table i = r.1 ∧ source table j = r.2 ∧
      (i,j) ∈ CommonRoleDynamicIndexSource.edges table requests :=
  CommonRoleDynamicIndexSource.scoped_request_present table requests
    ((run_ok_iff ..).mp h).1 r hr

/-- Exact model contract for a successful result. It is not model existence. -/
theorem success_models (table : Table) (s : State table.length) (requests : Requests)
    (out : State table.length) (h : run table s requests = .ok out)
    (a : Slot table → Comp Common.model) :
    All Common.model a out.atoms ↔
      All Common.model a s.atoms ∧ CommonRoleSourceIdentity.Coherent table a ∧
      ∀ i, Derived table (CommonRoleSourceIdentity.extend table s) requests i →
        Common.Equivalent (a i).1 (.base .str) := by
  rw [((run_ok_iff ..).mp h).2]
  exact CommonRoleDynamicIndexSource.output_models ..

theorem success_executes (table : Table) (s : State table.length) (requests : Requests)
    (out : State table.length) (h : run table s requests = .ok out)
    (a : Slot table → Comp Common.model) (hm : All Common.model a out.atoms) :
    CommonRoleDynamicIndexSourceExecution.Executed table s requests
      (CommonRoleDynamicIndexSource.saturate table (CommonRoleSourceIdentity.extend table s) requests) := by
  apply CommonRoleDynamicIndexSourceExecution.saturate_executes table s requests a
  simpa [((run_ok_iff ..).mp h).2] using hm

/-- Diagnostics preserve input order and multiplicity; the set contract does
not select a language error policy. -/
theorem error_members (table : Table) (s : State table.length) (requests errors : Requests)
    (h : run table s requests = .error errors) (r : Nat × Nat) :
    r ∈ errors ↔ r ∈ requests ∧
      ¬ ∃ i j : Slot table, source table i = r.1 ∧ source table j = r.2 := by
  rw [((run_error_iff ..).mp h).2]
  exact missing_exact ..

/-- Scope is a property of the requested obligations, not their order or duplicates. -/
theorem scope_membership_invariant (table : Table) (left right : Requests)
    (same : ∀ r, r ∈ left ↔ r ∈ right) :
    missing table left = [] ↔ missing table right = [] := by
  rw [missing_nil_iff, missing_nil_iff]
  constructor
  · intro h r hr; exact h r ((same r).mpr hr)
  · intro h r hr; exact h r ((same r).mp hr)

theorem scope_example_valid : missing [10,10,20,30] [(10,20),(20,30)] = [] := by
  decide

theorem scope_example_missing :
    missing [10,10] [(10,20),(10,10),(30,10),(10,20)] = [(10,20),(30,10),(10,20)] := by
  decide

/-- Missing names produce an explicit failure even though graph compilation
by itself would silently omit those request edges. -/
theorem malformed_run (s : State 2) :
    run [10,10] s [(10,20),(10,10),(30,10),(10,20)] =
      .error [(10,20),(30,10),(10,20)] := by
  simp only [run, scope_example_missing]
  rfl

end Yulang.CommonRoleDynamicIndexCheckedSource
