import Yulang.CommonRoleCanonicalSourceGraph
import Yulang.CommonRoleSourceGrowth

/-! Append-only source allocation retains actual canonical graph identities,
including captured unknown roots. This module does not generate new constraints,
rebuild recursive graphs, or prove declaration-driven allocation closure. -/
namespace Yulang.CommonRoleCanonicalSourceGrowth
open CommonRoleSourceIdentity
open CommonRoleSourceDescent
open CommonRoleCanonicalSourceGraph
open CommonRoleGraphInspection
open Core.PresenceGeneration (Comp)

/-- The new occurrence's storage slot, before canonical root routing. -/
def allocated (table extra : Table) (i : Slot extra) : Slot (table ++ extra) :=
  ⟨table.length + i.val, by simp only [List.length_append]; omega⟩

theorem allocated_source (table extra : Table) (i : Slot extra) :
    source (table ++ extra) (allocated table extra i) = source extra i := by
  simp [source, allocated]

private theorem slots_append (table extra : Table) :
    List.finRange (table ++ extra).length =
      (List.finRange table.length).map (retain table extra) ++
        (List.finRange extra.length).map (allocated table extra) := by
  apply List.ext_getElem
  · simp
  · intro n h₁ h₂
    by_cases h : n < table.length
    · simp [h, retain]
    · simp [List.getElem_append, h, allocated]
      omega

/-- Lookup first searches the old table, then the newly allocated suffix. -/
theorem representative_append (table extra : Table) (name : Nat) :
    representative (table ++ extra) name =
      ((representative table name).map (retain table extra)).or
        ((representative extra name).map (allocated table extra)) := by
  unfold representative
  rw [slots_append]
  simp only [List.find?_append, List.find?_map]
  congr 3 <;> funext slot
  · simp [retain_source]
  · simp [allocated_source]

/-- First-occurrence lookup is stable for every previously represented name. -/
theorem representative_retained (table extra : Table) (name : Nat) (i : Slot table)
    (found : representative table name = some i) :
    representative (table ++ extra) name = some (retain table extra i) := by
  rw [representative_append, found]
  rfl

/-- Exact retained numeric root, not just equality of source names or readouts. -/
theorem canonical_retained (table extra : Table) (i : Slot table) :
    canonical (table ++ extra) (retain table extra i) =
      retain table extra (canonical table i) := by
  obtain ⟨first, found⟩ := representative_exists table i
  have grown := representative_retained table extra (source table i) first found
  simp only [canonical, retain_source, grown, found, Option.getD_some]

/-- Newly allocated aliases of old names use the already existing root. -/
theorem allocated_alias_root (table extra : Table) (old : Slot table) (new : Slot extra)
    (same : source extra new = source table old) :
    canonical (table ++ extra) (allocated table extra new) =
      retain table extra (canonical table old) := by
  rw [← canonical_retained]
  apply (canonical_eq_iff ..).mpr
  rw [allocated_source, retain_source]
  exact same

/-- A genuinely new name uses its first occurrence in the appended suffix. -/
theorem allocated_fresh_root (table extra : Table) (new : Slot extra)
    (fresh : representative table (source extra new) = none) :
    canonical (table ++ extra) (allocated table extra new) =
      allocated table extra (canonical extra new) := by
  obtain ⟨first, found⟩ := representative_exists extra new
  simp only [canonical, allocated_source, representative_append, fresh, found,
    Option.map_none, Option.map_some, Option.getD_some]
  rfl

/-- Incremental allocation looks in the old table first. It does not rescan the
entire expanded table to compute a new occurrence's root. -/
def newRoot (table extra : Table) (i : Slot extra) : Slot (table ++ extra) :=
  match representative table (source extra i) with
  | some old => retain table extra old
  | none => allocated table extra (canonical extra i)

/-- Incremental root allocation exactly equals rebuilding the canonical map. -/
theorem newRoot_exact (table extra : Table) (i : Slot extra) :
    newRoot table extra i = canonical (table ++ extra) (allocated table extra i) := by
  cases h : representative table (source extra i) with
  | none => simpa only [newRoot,h] using (allocated_fresh_root table extra i h).symm
  | some old =>
    have found := representative_retained table extra (source extra i) old h
    simp only [newRoot, h, canonical, allocated_source, found, Option.getD_some]

/-- Incrementally created roots coincide exactly for equal source names. -/
theorem newRoot_identity_exact (table extra : Table) (i j : Slot extra) :
    newRoot table extra i = newRoot table extra j ↔ source extra i = source extra j := by
  rw [newRoot_exact, newRoot_exact, canonical_eq_iff, allocated_source, allocated_source]

/-- Comparing a new root with an old root uses source identity, not a known type. -/
theorem newRoot_old_exact (table extra : Table) (i : Slot extra) (j : Slot table) :
    newRoot table extra i = retain table extra (canonical table j) ↔
      source extra i = source table j := by
  rw [newRoot_exact, ← canonical_retained, canonical_eq_iff, allocated_source, retain_source]

/-- Reindex every capture and cycle reference without changing observations. -/
def retainObservation (table extra : Table) : Observation table.length →
    Observation (table ++ extra).length
  | .matched captures => .matched (captures.map fun c => (c.1, retain table extra c.2))
  | .mismatch => .mismatch
  | .unresolved => .unresolved
  | .cycle i => .cycle (retain table extra i)

/-- Canonical routing commutes with allocation for arbitrary observation payloads. -/
theorem route_retained (table extra : Table) (o : Observation table.length) :
    route (table ++ extra) (retainObservation table extra o) =
      retainObservation table extra (route table o) := by
  cases o <;> simp [route, retainObservation, List.map_map, canonical_retained]

/-- The actual variable inspector retains an old canonical capture literally,
even when graphs contain unknown nodes or change their scalar observations. -/
theorem variable_capture_retained (table extra : Table)
    (oldGraph : CommonRoleRegularGraph.Graph table.length)
    (newGraph : CommonRoleRegularGraph.Graph (table ++ extra).length)
    (name : Nat) (i : Slot table) :
    inspect newGraph (.variable name)
      (canonical (table ++ extra) (retain table extra i)) =
      retainObservation table extra (inspect oldGraph (.variable name) (canonical table i)) := by
  simp [inspect, retainObservation, canonical_retained]

/-- Multiple shared names keep their order, duplicates, and exact old root. -/
theorem shared_capture_retained (table extra : Table)
    (oldGraph : CommonRoleRegularGraph.Graph table.length)
    (newGraph : CommonRoleRegularGraph.Graph (table ++ extra).length)
    (names : List Nat) (i : Slot table) :
    inspect newGraph (.shared names)
      (canonical (table ++ extra) (retain table extra i)) =
      retainObservation table extra (inspect oldGraph (.shared names) (canonical table i)) := by
  simp [inspect, retainObservation, canonical_retained, List.map_map]

/-- Allocation preserves the entire computation at every old canonical root.
No coherence premise is needed: this is literal storage retention. -/
theorem canonical_value_retained (table extra : Table)
    (values : Slot table → Comp Common.model) (fallback : Comp Common.model)
    (i : Slot table) :
    CommonRoleSourceGrowth.grow table extra values fallback
      (canonical (table ++ extra) (retain table extra i)) = values (canonical table i) := by
  rw [canonical_retained]
  have h := congrFun (CommonRoleSourceGrowth.restrict_grow table extra values fallback)
    (canonical table i)
  exact h

/-- A new alias reads the old canonical computation, not the fallback. -/
theorem allocated_alias_value (table extra : Table)
    (values : Slot table → Comp Common.model) (fallback : Comp Common.model)
    (old : Slot table) (new : Slot extra)
    (same : source extra new = source table old) :
    CommonRoleSourceGrowth.grow table extra values fallback
      (canonical (table ++ extra) (allocated table extra new)) =
        values (canonical table old) := by
  rw [allocated_alias_root table extra old new same]
  exact congrFun (CommonRoleSourceGrowth.restrict_grow table extra values fallback)
    (canonical table old)

/-- Every coherent old source model extends while preserving all canonical root
values. Arbitrary duplicates and fresh names may occur in the finite suffix. -/
theorem coherent_canonical_extension (table extra : Table)
    (values : Slot table → Comp Common.model) (fallback : Comp Common.model) :
    Coherent table values ↔
      ∃ extended : Slot (table ++ extra) → Comp Common.model,
        CommonRoleSourceGrowth.restrict table extra extended = values ∧
        Coherent (table ++ extra) extended ∧
        ∀ i, extended (canonical (table ++ extra) (retain table extra i)) =
          values (canonical table i) := by
  constructor
  · intro coherent
    exact ⟨CommonRoleSourceGrowth.grow table extra values fallback,
      CommonRoleSourceGrowth.restrict_grow table extra values fallback,
      CommonRoleSourceGrowth.grow_coherent table extra values fallback coherent,
      canonical_value_retained table extra values fallback⟩
  · rintro ⟨extended, kept, coherent, _⟩
    rw [← kept]
    exact CommonRoleSourceGrowth.restrict_coherent table extra extended coherent

/-- Independent arbitrary old constraints and exact root retention hold together.
This is allocation only: no additional child constraints are silently asserted. -/
theorem solver_and_roots_exact (table extra : Table)
    (state : CommonRoleSettledConstraints.State table.length)
    (fallback : Comp Common.model) :
    (CommonRoleOpenPropagation.consistent (CommonRoleSourceGrowth.growState table extra state) =
      true ↔ CommonRoleOpenPropagation.consistent (extend table state) = true) ∧
    ∀ i, canonical (table ++ extra) (retain table extra i) =
      retain table extra (canonical table i) :=
  ⟨CommonRoleSourceGrowth.solver_growth_exact table extra state fallback,
    canonical_retained table extra⟩

/-- Duplicate new occurrences reuse old roots; genuinely new names receive a new
first root. Unknown observations do not collapse these distinct identities. -/
theorem append_alias_regression :
    canonical ([7,7,9] ++ [9,7,11,11]) ⟨3,by decide⟩ = ⟨2,by decide⟩ ∧
    canonical ([7,7,9] ++ [9,7,11,11]) ⟨4,by decide⟩ = ⟨0,by decide⟩ ∧
    canonical ([7,7,9] ++ [9,7,11,11]) ⟨5,by decide⟩ = ⟨5,by decide⟩ ∧
    canonical ([7,7,9] ++ [9,7,11,11]) ⟨6,by decide⟩ = ⟨5,by decide⟩ := by
  decide

end Yulang.CommonRoleCanonicalSourceGrowth
