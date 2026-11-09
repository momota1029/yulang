import Yulang.CommonRoleDynamicIndexConsistentSource

/-! Explicit initial slot equalities participate in finite string receiver feedback.
Equality and source-alias moves preserve models; only named Index moves invoke
 the role producer. This is a finite string adapter, not general source lowering. -/
namespace Yulang.CommonRoleDynamicIndexEqualitySource
open CommonRoleSourceIdentity (Table Slot source Coherent)
open CommonRoleSettledConstraints (State)
open CommonRoleOrdinaryKnownness (Evidence)
open CommonRoleDynamicIndexSource (Requests)
open CommonRoleDynamicIndexClosure (record)
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All)

abbrev Links (table : Table) := List (Slot table × Slot table)

def initial (table : Table) (seeds : List (Slot table)) (links : Links table) :=
  CommonRoleSourceIdentity.extend table
    (CommonRoleDynamicIndexConsistentSource.input seeds links)

def edges (table : Table) (links : Links table) (requests : Requests) :=
  CommonRoleDynamicIndexSource.edges table requests ++ links ++ links.map Prod.swap

theorem edges_exact (table : Table) (links : Links table) (requests : Requests)
    (i j : Slot table) : (i,j) ∈ edges table links requests ↔
      (source table i = source table j ∨ (source table i,source table j) ∈ requests) ∨
      (i,j) ∈ links ∨ (j,i) ∈ links := by
  simp [edges, CommonRoleDynamicIndexSource.edges_exact,
    List.mem_map, Prod.ext_iff, and_comm, and_assoc, or_assoc]

inductive Derived (table : Table) (seeds : List (Slot table)) (links : Links table)
    (requests : Requests) : Slot table → Prop where
  | seed : Evidence (initial table seeds links).atoms i .str → Derived table seeds links requests i
  | alias : source table i = source table j → Derived table seeds links requests i →
      Derived table seeds links requests j
  | equality : ((i,j) ∈ links ∨ (j,i) ∈ links) → Derived table seeds links requests i →
      Derived table seeds links requests j
  | index : (source table i,source table j) ∈ requests → Derived table seeds links requests i →
      Derived table seeds links requests j

theorem derived_exact (table : Table) (seeds : List (Slot table)) (links : Links table)
    (requests : Requests) (i : Slot table) :
    CommonRoleDynamicIndexClosure.Derived (initial table seeds links)
      (edges table links requests) i ↔ Derived table seeds links requests i := by
  constructor
  · intro h
    induction h with
    | seed h => exact .seed h
    | @index i j he _ ih =>
      rcases (edges_exact ..).mp he with (ha | hr) | he | he
      · exact .alias ha ih
      · exact .index hr ih
      · exact .equality (.inl he) ih
      · exact .equality (.inr he) ih
  · intro h
    induction h with
    | seed h => exact .seed h
    | alias h _ ih => exact .index ((edges_exact ..).mpr (.inl (.inl h))) ih
    | equality h _ ih => exact .index ((edges_exact ..).mpr (.inr h)) ih
    | index h _ ih => exact .index ((edges_exact ..).mpr (.inl (.inr h))) ih

def saturate (table : Table) (seeds : List (Slot table)) (links : Links table)
    (requests : Requests) :=
  CommonRoleDynamicIndexClosure.saturate (initial table seeds links) (edges table links requests)

def output (table : Table) (seeds : List (Slot table)) (links : Links table)
    (requests : Requests) :=
  CommonRoleDynamicIndexClosure.output (initial table seeds links) (edges table links requests)

theorem saturate_exact (table : Table) (seeds : List (Slot table)) (links : Links table)
    (requests : Requests) (i : Slot table) :
    i ∈ saturate table seeds links requests ↔ Derived table seeds links requests i := by
  rw [saturate, CommonRoleDynamicIndexClosure.saturate_exact, derived_exact]

theorem initial_models (table : Table) (seeds : List (Slot table)) (links : Links table)
    (a : Slot table → Comp Common.model) :
    All Common.model a (initial table seeds links).atoms ↔
      ((∀ i ∈ seeds, Common.Equivalent (a i).1 (.base .str)) ∧
       ∀ e ∈ links, Common.Equivalent (a e.1).1 (a e.2).1) ∧ Coherent table a := by
  rw [initial, CommonRoleSourceIdentity.extend_exact,
    CommonRoleDynamicIndexConsistentSource.input_models]

theorem output_models (table : Table) (seeds : List (Slot table)) (links : Links table)
    (requests : Requests) (a : Slot table → Comp Common.model) :
    All Common.model a (output table seeds links requests).atoms ↔
      All Common.model a (initial table seeds links).atoms ∧
      ∀ i, Derived table seeds links requests i → Common.Equivalent (a i).1 (.base .str) := by
  simp only [output, CommonRoleDynamicIndexClosure.output_models, derived_exact]

theorem output_has_model (table : Table) (seeds : List (Slot table)) (links : Links table)
    (requests : Requests) :
    All Common.model CommonRoleDynamicIndexConsistentSource.stringAssignment
      (output table seeds links requests).atoms := by
  apply (output_models ..).mpr
  refine ⟨(initial_models ..).mpr ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · exact fun _ _ => Common.equivalent_refl _
  · exact fun _ _ => Common.equivalent_refl _
  · exact fun _ _ _ => Common.equivalent_refl _
  · exact fun _ _ => Common.equivalent_refl _

/-- Transferring a recorded str fact along a type equality does not alter models. -/
theorem equality_models (table : Table) (seeds : List (Slot table)) (links : Links table)
    (xs : List (Slot table)) (i j : Slot table)
    (he : (i,j) ∈ links ∨ (j,i) ∈ links) (hi : i ∈ xs)
    (a : Slot table → Comp Common.model) :
    All Common.model a (record (initial table seeds links) (j :: xs)).atoms ↔
      All Common.model a (record (initial table seeds links) xs).atoms := by
  rw [record, CommonRoleCandidateStateFrontier.extend_exact]
  constructor
  · exact And.left
  · intro hm
    have h := (CommonRoleDynamicIndexClosure.record_models ..).mp hm
    have hl := ((initial_models ..).mp h.1).1.2
    have hij : Common.Equivalent (a j).1 (a i).1 := by
      rcases he with he | he
      · exact Common.equivalent_symm (hl _ he)
      · exact hl _ he
    exact ⟨hm, Common.equivalent_trans hij (h.2 i hi)⟩

inductive Executed (table : Table) (seeds : List (Slot table)) (links : Links table)
    (requests : Requests) : List (Slot table) → Prop where
  | nil : Executed table seeds links requests []
  | seed : Executed table seeds links requests xs →
      Evidence (initial table seeds links).atoms i .str → Executed table seeds links requests (i :: xs)
  | transfer : Executed table seeds links requests xs →
      (source table i = source table j ∨ (i,j) ∈ links ∨ (j,i) ∈ links) → i ∈ xs →
      (∀ a, All Common.model a (record (initial table seeds links) (j :: xs)).atoms ↔
        All Common.model a (record (initial table seeds links) xs).atoms) →
      Executed table seeds links requests (j :: xs)
  | index : Executed table seeds links requests xs → (source table i,source table j) ∈ requests →
      CommonRoleOrdinaryKnownness.produceIndex (record (initial table seeds links) xs) i j =
        some (record (initial table seeds links) (j :: xs)) →
      Executed table seeds links requests (j :: xs)

/-- Concrete consistency of this seed/equality fragment validates every producer read. -/
theorem trace_executes (table : Table) (seeds : List (Slot table)) (links : Links table)
    (requests : Requests) (xs : List (Slot table))
    (h : CommonRoleDynamicIndexClosure.Trace (initial table seeds links)
      (edges table links requests) xs) : Executed table seeds links requests xs := by
  have hm := output_has_model table seeds links requests
  have all := (CommonRoleDynamicIndexClosure.output_models ..).mp hm
  induction h with
  | nil => exact .nil
  | seed _ he ih => exact .seed ih he
  | @index xs i j hx he hi ih =>
    rcases (edges_exact ..).mp he with (ha | hr) | he | he
    · exact .transfer ih (.inl ha) hi
        (CommonRoleDynamicIndexSourceExecution.alias_models table
          (CommonRoleDynamicIndexConsistentSource.input seeds links) xs i j ha hi)
    · apply Executed.index ih hr
      apply CommonRoleOrdinaryKnownness.index_from_detected_str
      apply CommonRoleDynamicIndexClosure.detects_recorded (initial table seeds links) xs i hi
        CommonRoleDynamicIndexConsistentSource.stringAssignment
      exact (CommonRoleDynamicIndexClosure.record_models ..).mpr ⟨all.1, fun k hk =>
        all.2 k (CommonRoleDynamicIndexClosure.trace_derived _ _ xs hx k hk)⟩
    · exact .transfer ih (.inr (.inl he)) hi (equality_models table seeds links xs i j (.inl he) hi)
    · exact .transfer ih (.inr (.inr he)) hi (equality_models table seeds links xs i j (.inr he) hi)

theorem saturate_executes (table : Table) (seeds : List (Slot table)) (links : Links table)
    (requests : Requests) : Executed table seeds links requests (saturate table seeds links requests) :=
  trace_executes table seeds links requests _ (CommonRoleDynamicIndexClosure.saturate_trace ..)

theorem capacity (table : Table) (seeds : List (Slot table)) (links : Links table)
    (requests : Requests) : (saturate table seeds links requests).length ≤ table.length :=
  CommonRoleDynamicIndexClosure.capacity ..

theorem stopped (table : Table) (seeds : List (Slot table)) (links : Links table)
    (requests : Requests) :
    FiniteHorn.firstFresh (CommonRoleDynamicIndexClosure.rules (initial table seeds links)
      (edges table links requests)) (saturate table seeds links requests)
      (List.finRange table.length) = none := CommonRoleDynamicIndexClosure.stopped ..

theorem reachable_checked_step (table : Table) (seeds : List (Slot table)) (links : Links table)
    (requests : Requests) (i j : Slot table) (hi : Derived table seeds links requests i) :
    CommonRoleOrdinaryKnownness.checkedProduceIndex (output table seeds links requests) i j =
      some (CommonRoleCandidateStateFrontier.extend (output table seeds links requests) j .str) := by
  apply (CommonRoleOrdinaryKnownness.checked_exact ..).mpr
  constructor
  · exact CommonRoleDynamicIndexClosure.actual_index_step _ _ i j
      ((derived_exact ..).mpr hi) _ (output_has_model table seeds links requests)
  · exact ⟨CommonRoleDynamicIndexConsistentSource.stringAssignment,
      (CommonRoleCandidateStateFrontier.extend_exact ..).mpr
        ⟨output_has_model table seeds links requests, Common.equivalent_refl _⟩⟩

/-- Leastness ranges over all predicates closed under the four independent rules. -/
theorem least (table : Table) (seeds : List (Slot table)) (links : Links table)
    (requests : Requests) (P : Slot table → Prop)
    (hs : ∀ i, Evidence (initial table seeds links).atoms i .str → P i)
    (ha : ∀ i j, source table i = source table j → P i → P j)
    (he : ∀ i j, ((i,j) ∈ links ∨ (j,i) ∈ links) → P i → P j)
    (hr : ∀ i j, (source table i, source table j) ∈ requests → P i → P j) :
    ∀ i ∈ saturate table seeds links requests, P i := by
  intro i hi
  have h := (saturate_exact ..).mp hi
  clear hi
  induction h with
  | seed h => exact hs _ h
  | alias h _ ih => exact ha _ _ h ih
  | equality h _ ih => exact he _ _ h ih
  | index h _ ih => exact hr _ _ h ih

/-- Re-running the same graph at its output changes no fact membership.
No model premise is needed; list order and atom multiplicity are not identified. -/
theorem output_fixed (table : Table) (seeds : List (Slot table)) (links : Links table)
    (requests : Requests) (i : Slot table) :
    i ∈ CommonRoleDynamicIndexClosure.saturate (output table seeds links requests)
      (edges table links requests) ↔ i ∈ saturate table seeds links requests :=
  CommonRoleDynamicIndexClosure.saturate_output_fixed ..

/-- The earlier adapter did not use the explicit equality as a feedback edge. -/
theorem earlier_equality_pending :
    CommonRoleOrdinaryKnownness.produceIndex
      (CommonRoleDynamicIndexSource.output [10,20,30]
        (CommonRoleDynamicIndexConsistentSource.input [0] [(1,0)]) [(20,30)]) 1 2 = none := by
  decide

/-- A reversed equality activates an otherwise unseeded Index receiver. -/
theorem reverse_equality_reaches :
    Derived [10,20,30] [0] [(1,0)] [(20,30)] 2 := by
  apply (saturate_exact ..).mp
  decide

theorem reverse_equality_checked :
    CommonRoleOrdinaryKnownness.checkedProduceIndex
      (output [10,20,30] [0] [(1,0)] [(20,30)]) 1 2 =
      some (CommonRoleCandidateStateFrontier.extend
        (output [10,20,30] [0] [(1,0)] [(20,30)]) 2 .str) := by
  apply reachable_checked_step
  apply (saturate_exact ..).mp
  decide

end Yulang.CommonRoleDynamicIndexEqualitySource
