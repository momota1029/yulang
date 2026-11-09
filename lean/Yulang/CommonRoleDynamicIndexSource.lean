import Yulang.CommonRoleDynamicIndexClosure
import Yulang.CommonRoleSourceIdentity

/-! A finite named-source adapter for the string Index fragment.
The source table and named requests are inputs, not a parser correctness result.
Alias edges share source identity; request edges retain their named provenance. -/
namespace Yulang.CommonRoleDynamicIndexSource
open CommonRoleSourceIdentity (Table Slot source Coherent)
open CommonRoleSettledConstraints (State)
open CommonRoleOrdinaryKnownness (Evidence)
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All)

abbrev Requests := List (Nat × Nat)

def edges (table : Table) (requests : Requests) : CommonRoleDynamicIndexClosure.Edges table.length :=
  (List.finRange table.length).flatMap fun i =>
    (List.finRange table.length).filterMap fun j =>
      if source table i = source table j ∨ (source table i, source table j) ∈ requests
      then some (i,j) else none

theorem edges_exact (table : Table) (requests : Requests) (i j : Slot table) :
    (i,j) ∈ edges table requests ↔
      source table i = source table j ∨ (source table i, source table j) ∈ requests := by
  simp [edges]

inductive Derived (table : Table) (s : State table.length) (requests : Requests) :
    Slot table → Prop where
  | seed : Evidence s.atoms i .str → Derived table s requests i
  | alias : source table i = source table j → Derived table s requests i →
      Derived table s requests j
  | index : (source table i, source table j) ∈ requests → Derived table s requests i →
      Derived table s requests j

theorem derived_exact (table : Table) (s : State table.length) (requests : Requests)
    (i : Slot table) :
    CommonRoleDynamicIndexClosure.Derived s (edges table requests) i ↔ Derived table s requests i := by
  constructor
  · intro h
    induction h with
    | seed h => exact .seed h
    | @index i j he _ ih =>
      rcases (edges_exact table requests i j).mp he with h | h
      · exact .alias h ih
      · exact .index h ih
  · intro h
    induction h with
    | seed h => exact .seed h
    | @alias i j h _ ih => exact .index ((edges_exact ..).mpr (.inl h)) ih
    | @index i j h _ ih => exact .index ((edges_exact ..).mpr (.inr h)) ih

def saturate (table : Table) (s : State table.length) (requests : Requests) :=
  CommonRoleDynamicIndexClosure.saturate s (edges table requests)

theorem saturate_exact (table : Table) (s : State table.length) (requests : Requests)
    (i : Slot table) : i ∈ saturate table s requests ↔ Derived table s requests i := by
  rw [saturate, CommonRoleDynamicIndexClosure.saturate_exact, derived_exact]

theorem alias_closed (table : Table) (s : State table.length) (requests : Requests)
    (i j : Slot table) (same : source table i = source table j)
    (hi : i ∈ saturate table s requests) : j ∈ saturate table s requests :=
  (saturate_exact ..).mpr (.alias same ((saturate_exact ..).mp hi))

theorem request_closed (table : Table) (s : State table.length) (requests : Requests)
    (i j : Slot table) (request : (source table i,source table j) ∈ requests)
    (hi : i ∈ saturate table s requests) : j ∈ saturate table s requests :=
  (saturate_exact ..).mpr (.index request ((saturate_exact ..).mp hi))

def output (table : Table) (s : State table.length) (requests : Requests) : State table.length :=
  CommonRoleDynamicIndexClosure.output (CommonRoleSourceIdentity.extend table s) (edges table requests)

theorem output_models (table : Table) (s : State table.length) (requests : Requests)
    (a : Slot table → Comp Common.model) :
    All Common.model a (output table s requests).atoms ↔
      All Common.model a s.atoms ∧ Coherent table a ∧
      ∀ i, Derived table (CommonRoleSourceIdentity.extend table s) requests i →
        Common.Equivalent (a i).1 (.base .str) := by
  simp only [output, CommonRoleDynamicIndexClosure.output_models, CommonRoleSourceIdentity.extend_exact, derived_exact]
  exact and_assoc

theorem output_coherent (table : Table) (s : State table.length) (requests : Requests)
    (a : Slot table → Comp Common.model)
    (h : All Common.model a (output table s requests).atoms) : Coherent table a :=
  ((output_models ..).mp h).2.1

theorem capacity (table : Table) (s : State table.length) (requests : Requests) :
    (saturate table s requests).length ≤ table.length := CommonRoleDynamicIndexClosure.capacity ..

theorem stopped (table : Table) (s : State table.length) (requests : Requests) :
    FiniteHorn.firstFresh (CommonRoleDynamicIndexClosure.rules s (edges table requests)) (saturate table s requests)
      (List.finRange table.length) = none := CommonRoleDynamicIndexClosure.stopped ..

/-- Every requested source name has at least one occurrence slot. Without this
condition, requests with absent endpoints produce no compiled edge. -/
def WellScoped (table : Table) (requests : Requests) : Prop :=
  ∀ r ∈ requests, ∃ i j : Slot table, source table i = r.1 ∧ source table j = r.2

theorem scoped_request_present (table : Table) (requests : Requests)
    (hscope : WellScoped table requests) (r : Nat × Nat) (hr : r ∈ requests) :
    ∃ i j : Slot table, source table i = r.1 ∧ source table j = r.2 ∧
      (i,j) ∈ edges table requests := by
  obtain ⟨i,j,hi,hj⟩ := hscope r hr
  refine ⟨i,j,hi,hj,(edges_exact ..).mpr (.inr ?_)⟩
  simpa [hi,hj] using hr

theorem named_request_all_occurrences (table : Table) (s : State table.length)
    (requests : Requests) (r : Nat × Nat) (hr : r ∈ requests)
    (i j : Slot table) (hi : source table i = r.1) (hj : source table j = r.2)
    (derived : Derived table s requests i) : Derived table s requests j := by
  exact .index (by simpa [hi,hj] using hr) derived

end Yulang.CommonRoleDynamicIndexSource
