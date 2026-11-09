import Yulang.CommonRoleDynamicIndexSourceSemantics

/-! Exact model preservation for the finite positive string/equality fragment.
Residual request implications are kept separately from ordinary atoms. This is
an internal source adapter, not the general Index or final diagnostic semantics.
The restricted payload and initial-state domain are proof-fragment limitations,
not additional language rejection rules. -/
namespace Yulang.CommonRoleDynamicIndexResidualSource
open CommonRoleSourceIdentity (Table Slot source)
open CommonRoleDynamicIndexSource (Requests WellScoped)
open CommonRoleDynamicIndexEqualitySource (Links initial output saturate Derived)
open CommonRoleDynamicIndexSourceSemantics (SourceModel ForcesString)
open CommonRoleDynamicIndexCheckedSource (missing missing_nil_iff)
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All)

/-- Enumerate every represented occurrence, retaining aliases as distinct slots. -/
def pairs (table : Table) (requests : Requests) : List (Slot table × Slot table) :=
  (List.finRange table.length).flatMap fun i =>
    (List.finRange table.length).filterMap fun j =>
      if (source table i, source table j) ∈ requests then some (i,j) else none

theorem pairs_exact (table : Table) (requests : Requests) (i j : Slot table) :
    (i,j) ∈ pairs table requests ↔ (source table i, source table j) ∈ requests := by
  simp [pairs]

/-- Only requests whose receivers are not reached remain conditional. -/
def residual (table : Table) (seeds : List (Slot table)) (links : Links table)
    (requests : Requests) : List (Slot table × Slot table) :=
  (pairs table requests).filter fun p => p.1 ∉ saturate table seeds links requests

theorem residual_exact (table : Table) (seeds : List (Slot table)) (links : Links table)
    (requests : Requests) (i j : Slot table) :
    (i,j) ∈ residual table seeds links requests ↔
      (source table i, source table j) ∈ requests ∧ ¬ Derived table seeds links requests i := by
  simp [residual, pairs_exact, CommonRoleDynamicIndexEqualitySource.saturate_exact]

/-- Residuals are precisely the original requests pending in the actual checker. -/
theorem residual_checked_exact (table : Table) (seeds : List (Slot table))
    (links : Links table) (requests : Requests) (i j : Slot table) :
    (i,j) ∈ residual table seeds links requests ↔
      (source table i, source table j) ∈ requests ∧
      CommonRoleOrdinaryKnownness.checkedProduceIndex
        (output table seeds links requests) i j = none := by
  rw [residual_exact, CommonRoleDynamicIndexSourceSemantics.checked_pending_iff,
    CommonRoleDynamicIndexSourceSemantics.source_underdetermined_iff,
    CommonRoleDynamicIndexSourceSemantics.source_forces_iff]

structure Packet (table : Table) where
  state : CommonRoleSettledConstraints.State table.length
  pending : List (Slot table × Slot table)

def build (table : Table) (seeds : List (Slot table)) (links : Links table)
    (requests : Requests) : Packet table :=
  ⟨output table seeds links requests, residual table seeds links requests⟩

/-- A residual pair keeps its implication; it is not encoded as an unconditional
target equality. Models may still refine an unresolved receiver to string. -/
def Models (table : Table) (packet : Packet table) (a : Slot table → Comp Common.model) : Prop :=
  All Common.model a packet.state.atoms ∧
    ∀ p ∈ packet.pending, Common.Equivalent (a p.1).1 (.base .str) →
      Common.Equivalent (a p.2).1 (.base .str)

/-- Full source-model equality, rather than just equality of string consequences.
Quantification includes empty tables, duplicate names, cycles, and unreachable slots.
Absent names are diagnosed separately by run, not silently certified here. -/
theorem build_models_exact (table : Table) (seeds : List (Slot table))
    (links : Links table) (requests : Requests) (a : Slot table → Comp Common.model) :
    Models table (build table seeds links requests) a ↔
      SourceModel table seeds links requests a := by
  constructor
  · rintro ⟨ha, hp⟩
    have ho := (CommonRoleDynamicIndexEqualitySource.output_models ..).mp ha
    have hi := (CommonRoleDynamicIndexEqualitySource.initial_models ..).mp ho.1
    refine ⟨hi.1.1, hi.1.2, hi.2, ?_⟩
    intro i j hr hs
    by_cases hd : Derived table seeds links requests i
    · exact ho.2 j (.index hr hd)
    · exact hp (i,j) ((residual_exact ..).mpr ⟨hr, hd⟩) hs
  · intro hm
    refine ⟨CommonRoleDynamicIndexSourceSemantics.source_models_output table seeds links requests a hm, ?_⟩
    intro p hp hs
    exact hm.requests p.1 p.2 ((residual_exact ..).mp hp).1 hs

/-- The executable scope check guards the richer result without choosing a
language-visible error policy. It reports the existing ordered missing list. -/
def run (table : Table) (seeds : List (Slot table)) (links : Links table)
    (requests : Requests) : Except Requests (Packet table) :=
  if missing table requests = [] then .ok (build table seeds links requests)
  else .error (missing table requests)

theorem run_ok_iff (table : Table) (seeds : List (Slot table)) (links : Links table)
    (requests : Requests) (packet : Packet table) :
    run table seeds links requests = .ok packet ↔
      WellScoped table requests ∧ packet = build table seeds links requests := by
  unfold run
  split
  · rename_i h
    simp only [Except.ok.injEq]
    exact ⟨fun he => ⟨(missing_nil_iff ..).mp h, he.symm⟩, fun he => he.2.symm⟩
  · rename_i h
    constructor
    · intro he; cases he
    · intro he; exact False.elim (h ((missing_nil_iff ..).mpr he.1))

/-- No externally supplied satisfiability assumption is needed by this entrance. -/
theorem run_success_iff (table : Table) (seeds : List (Slot table)) (links : Links table)
    (requests : Requests) :
    (∃ packet, run table seeds links requests = .ok packet) ↔ WellScoped table requests := by
  constructor
  · rintro ⟨packet, h⟩; exact ((run_ok_iff ..).mp h).1
  · intro h; exact ⟨build table seeds links requests, (run_ok_iff ..).mpr ⟨h,rfl⟩⟩

theorem run_models_exact (table : Table) (seeds : List (Slot table)) (links : Links table)
    (requests : Requests) (packet : Packet table)
    (h : run table seeds links requests = .ok packet) (a : Slot table → Comp Common.model) :
    Models table packet a ↔ SourceModel table seeds links requests a := by
  rw [((run_ok_iff ..).mp h).2]
  exact build_models_exact ..

theorem run_has_model (table : Table) (seeds : List (Slot table)) (links : Links table)
    (requests : Requests) (packet : Packet table)
    (h : run table seeds links requests = .ok packet) :
    Models table packet CommonRoleDynamicIndexConsistentSource.stringAssignment :=
  (run_models_exact table seeds links requests packet h _).mpr
    (CommonRoleDynamicIndexSourceSemantics.string_source_model ..)

/-- Successful scope checking accounts for every original named request:
each occurrence pair is either pending or actually succeeds, never discarded. -/
theorem run_covers_requests (table : Table) (seeds : List (Slot table)) (links : Links table)
    (requests : Requests) (packet : Packet table)
    (h : run table seeds links requests = .ok packet) (r : Nat × Nat) (hr : r ∈ requests) :
    ∃ i j : Slot table, source table i = r.1 ∧ source table j = r.2 ∧
      ((i,j) ∈ packet.pending ∨ ∃ out,
        CommonRoleOrdinaryKnownness.checkedProduceIndex packet.state i j = some out) := by
  obtain ⟨scope, rfl⟩ := (run_ok_iff ..).mp h
  obtain ⟨i,j,hi,hj⟩ := scope r hr
  refine ⟨i,j,hi,hj,?_⟩
  by_cases hd : Derived table seeds links requests i
  · exact .inr ((CommonRoleDynamicIndexSemanticSource.checked_success_iff ..).mpr hd)
  · exact .inl ((residual_exact ..).mpr ⟨by simpa [hi,hj] using hr, hd⟩)

/-- Source clauses, hence packet models, ignore ordering and multiplicity of
named requests. The executable lists themselves are not equated. -/
theorem model_order_independent (table : Table) (seeds : List (Slot table))
    (links : Links table) (left right : Requests)
    (same : ∀ r, r ∈ left ↔ r ∈ right) (a : Slot table → Comp Common.model) :
    Models table (build table seeds links left) a ↔
      Models table (build table seeds links right) a := by
  rw [build_models_exact, build_models_exact]
  constructor
  · intro h; exact ⟨h.seeds, h.equalities, h.aliases,
      fun i j hr hs => h.requests i j ((same _).mpr hr) hs⟩
  · intro h; exact ⟨h.seeds, h.equalities, h.aliases,
      fun i j hr hs => h.requests i j ((same _).mp hr) hs⟩

/-- The cycle49 boundary witness cannot slip through the richer result. -/
theorem atom_only_loss_repaired :
    ∃ a : Slot [10,20] → Comp Common.model,
      All Common.model a (output [10,20] [] [] [(10,20)]).atoms ∧
      ¬ Models [10,20] (build [10,20] [] [] [(10,20)]) a := by
  obtain ⟨a,ha,hn⟩ := CommonRoleDynamicIndexSourceSemantics.output_models_not_source_models
  exact ⟨a,ha,fun hm => hn ((build_models_exact ..).mp hm)⟩

theorem residual_unseeded : residual [10,20] [] [] [(10,20)] = [(0,1)] := by decide

theorem residual_chain_closed :
    residual [10,10,20,30] [0] [] [(10,20),(20,30)] = [] := by decide

theorem dangling_names_reported :
    run [10,10] [] [] [(10,20),(10,10),(30,10),(10,20)] =
      .error [(10,20),(30,10),(10,20)] := by
  simp only [run, CommonRoleDynamicIndexCheckedSource.scope_example_missing]
  rfl

end Yulang.CommonRoleDynamicIndexResidualSource
