import Yulang.CommonRoleDynamicIndexResidualBatches

/-! Exact residual membership after finite batches. The fixed finite carrier,
positive string seeds and type equalities are implementation/proof-fragment
limits, not language rejection rules. This module preserves source obligation
coverage but does not define the general language-visible four-way diagnostic. -/
namespace Yulang.CommonRoleDynamicIndexResidualFrontier
open CommonRoleSourceIdentity (Table Slot source)
open CommonRoleDynamicIndexResidualBatches
open CommonRoleDynamicIndexSourceSemantics (SourceModel ForcesString)
open CommonRoleDynamicIndexResidualSource (Packet)
open Core.PresenceGeneration (Comp)

/-- Any source model with a non-string receiver prevents compaction from
removing that represented request. Both endpoints range over all source slots. -/
theorem compact_requests_unknown (table : Table) (p : Problem table)
    (a : Slot table → Comp Common.model) (ha : Satisfies table p a)
    (i j : Slot table) (unknown : ¬ Common.Equivalent (a i).1 (.base .str)) :
    (source table i, source table j) ∈ (compact table p).requests ↔
      (source table i, source table j) ∈ p.requests := by
  change _ ∈ CommonRoleDynamicIndexResidualResume.pendingNames table _ _ _ ↔ _
  rw [CommonRoleDynamicIndexResidualResume.pending_names_exact,
    CommonRoleDynamicIndexResidualSource.residual_exact]
  have hn : ¬ CommonRoleDynamicIndexEqualitySource.Derived table p.seeds p.links p.requests i := by
    intro hd
    exact unknown (CommonRoleDynamicIndexSourceSemantics.derived_sound
      table p.seeds p.links p.requests i hd a ha)
  simp only [hn, not_false_eq_true, and_true]

/-- Flattening is only bookkeeping: request membership includes every supplied
batch, even if an earlier round already discharged its receiver. -/
theorem appendMany_requests (table : Table) (updates : List (Problem table))
    (p : Problem table) (r : Nat × Nat) :
    r ∈ (appendMany table p updates).requests ↔
      r ∈ p.requests ∨ ∃ u ∈ updates, r ∈ u.requests := by
  induction updates generalizing p with
  | nil => simp [appendMany]
  | cons u rest ih =>
    simp only [appendMany, ih, append, List.mem_append, List.mem_cons,
      exists_eq_or_imp]
    exact or_assoc

/-- A single countermodel of the whole accumulated input witnesses retention
of every still-unknown original request through all intermediate compactions. -/
theorem advanceMany_requests_unknown (table : Table) (updates : List (Problem table))
    (p : Problem table) (a : Slot table → Comp Common.model)
    (ha : Satisfies table (appendMany table p updates) a)
    (i j : Slot table) (unknown : ¬ Common.Equivalent (a i).1 (.base .str)) :
    (source table i, source table j) ∈ (advanceMany table p updates).requests ↔
      (source table i, source table j) ∈ (appendMany table p updates).requests := by
  induction updates generalizing p with
  | nil => rfl
  | cons u rest ih =>
    have hfull := (appendMany_models table (u :: rest) p a).mp ha
    have hp := hfull.1
    have hu := hfull.2 u (by simp)
    have hnext : Satisfies table (appendMany table (advance table p u) rest) a := by
      apply (appendMany_models ..).mpr
      refine ⟨(advance_models ..).mpr ((append_models ..).mpr ⟨hp,hu⟩), ?_⟩
      intro q hq
      exact hfull.2 q (by simp [hq])
    change _ ∈ (advanceMany table (advance table p u) rest).requests ↔ _
    rw [ih (advance table p u) hnext]
    simp only [appendMany_requests, advance, append, List.mem_append,
      List.mem_cons, exists_eq_or_imp]
    rw [compact_requests_unknown table p a hp i j unknown]
    exact or_assoc

/-- Every final pending pair is exactly an original represented obligation with
an underdetermined receiver, not merely a request still in the compacted input. -/
theorem solve_residual_exact (table : Table) (p : Problem table)
    (updates : List (Problem table)) (i j : Slot table) :
    (i,j) ∈ (solve table p updates).pending ↔
      (source table i, source table j) ∈ (appendMany table p updates).requests ∧
      ¬ ForcesString table (appendMany table p updates).seeds
        (appendMany table p updates).links (appendMany table p updates).requests i := by
  classical
  let final := advanceMany table p updates
  let original := appendMany table p updates
  have hforce : ForcesString table final.seeds final.links final.requests i ↔
      ForcesString table original.seeds original.links original.requests i := by
    constructor
    · intro h a ha
      exact h a ((advanceMany_models table updates p a).mpr ha)
    · intro h a ha
      exact h a ((advanceMany_models table updates p a).mp ha)
  change (i,j) ∈ CommonRoleDynamicIndexResidualSource.residual table
    final.seeds final.links final.requests ↔ _
  rw [CommonRoleDynamicIndexResidualSource.residual_exact,
    ← CommonRoleDynamicIndexSourceSemantics.source_forces_iff, hforce]
  constructor
  · rintro ⟨hr,hn⟩
    refine ⟨?_,hn⟩
    have witness : ∃ a, Satisfies table original a ∧
        ¬ Common.Equivalent (a i).1 (.base .str) := by
      apply Classical.byContradiction
      intro absent
      apply hn
      intro a ha
      apply Classical.byContradiction
      intro hu
      exact absent ⟨a,ha,hu⟩
    obtain ⟨a,ha,hu⟩ := witness
    exact (advanceMany_requests_unknown table updates p a ha i j hu).mp hr
  · rintro ⟨hr,hn⟩
    refine ⟨?_,hn⟩
    have witness : ∃ a, Satisfies table original a ∧
        ¬ Common.Equivalent (a i).1 (.base .str) := by
      apply Classical.byContradiction
      intro absent
      apply hn
      intro a ha
      apply Classical.byContradiction
      intro hu
      exact absent ⟨a,ha,hu⟩
    obtain ⟨a,ha,hu⟩ := witness
    exact (advanceMany_requests_unknown table updates p a ha i j hu).mpr hr

/-- Pending list membership includes original obligation membership and two
independent source models that disagree on the receiver type. -/
theorem solve_pending_countermodels (table : Table) (p : Problem table)
    (updates : List (Problem table)) (i j : Slot table) :
    (i,j) ∈ (solve table p updates).pending ↔
      (source table i, source table j) ∈ (appendMany table p updates).requests ∧
      ∃ a b : Slot table → Comp Common.model,
        Satisfies table (appendMany table p updates) a ∧
        Satisfies table (appendMany table p updates) b ∧
        ¬ Common.Equivalent (a i).1 (b i).1 := by
  rw [solve_residual_exact, ← CommonRoleDynamicIndexSourceSemantics.source_underdetermined_iff]
  rfl

/-- The actual executable pending list and real checked execution agree for
precisely the represented original obligations, even after compaction. -/
theorem solve_residual_checked (table : Table) (p : Problem table)
    (updates : List (Problem table)) (i j : Slot table) :
    (i,j) ∈ (solve table p updates).pending ↔
      (source table i, source table j) ∈ (appendMany table p updates).requests ∧
      CommonRoleOrdinaryKnownness.checkedProduceIndex
        (solve table p updates).state i j = none := by
  rw [solve_pending_countermodels, solve_pending_exact]

/-- A successful checked entrance inherits exact original-source residual
semantics. Scope checking is the only execution premise, not a model oracle. -/
theorem run_residual_exact (table : Table) (p : Problem table)
    (updates : List (Problem table)) (packet : Packet table)
    (h : run table p updates = .ok packet) (i j : Slot table) :
    (i,j) ∈ packet.pending ↔
      (source table i, source table j) ∈ (appendMany table p updates).requests ∧
      ¬ ForcesString table (appendMany table p updates).seeds
        (appendMany table p updates).links (appendMany table p updates).requests i := by
  rw [((run_ok_iff ..).mp h).2]
  exact solve_residual_exact ..

/-- Every original named request is represented in a successful result and is
either retained pending or actually checked successfully. No earlier discharged
request is mistaken for a missing obligation. This is not dictionary soundness. -/
theorem run_covers_original_requests (table : Table) (p : Problem table)
    (updates : List (Problem table)) (packet : Packet table)
    (h : run table p updates = .ok packet) (r : Nat × Nat)
    (hr : r ∈ (appendMany table p updates).requests) :
    ∃ i j : Slot table, source table i = r.1 ∧ source table j = r.2 ∧
      ((i,j) ∈ packet.pending ∨ ∃ out,
        CommonRoleOrdinaryKnownness.checkedProduceIndex packet.state i j = some out) := by
  obtain ⟨scope,rfl⟩ := (run_ok_iff ..).mp h
  obtain ⟨i,j,hi,hj⟩ := scope r hr
  refine ⟨i,j,hi,hj,?_⟩
  cases hc : CommonRoleOrdinaryKnownness.checkedProduceIndex (solve table p updates).state i j with
  | none =>
    exact .inl ((solve_residual_checked ..).mpr ⟨by simpa [hi,hj] using hr,hc⟩)
  | some out => exact .inr ⟨out,rfl⟩

/-- Reordering the supplied batches preserves pending pair membership, not
only whole-packet models. Source aliases and cyclic requests remain allowed.
The theorem does not assert serialized dictionary or atom-list equality. -/
theorem update_order_pending (table : Table) (p : Problem table)
    (left right : List (Problem table)) (same : ∀ u, u ∈ left ↔ u ∈ right)
    (i j : Slot table) :
    (i,j) ∈ (solve table p left).pending ↔ (i,j) ∈ (solve table p right).pending := by
  have hr : (source table i, source table j) ∈ (appendMany table p left).requests ↔
      (source table i, source table j) ∈ (appendMany table p right).requests := by
    simp only [appendMany_requests]
    constructor
    · rintro (hp | ⟨u,hu,hq⟩)
      · exact .inl hp
      · exact .inr ⟨u,(same u).mp hu,hq⟩
    · rintro (hp | ⟨u,hu,hq⟩)
      · exact .inl hp
      · exact .inr ⟨u,(same u).mpr hu,hq⟩
  have hf : ForcesString table (appendMany table p left).seeds
      (appendMany table p left).links (appendMany table p left).requests i ↔
      ForcesString table (appendMany table p right).seeds
        (appendMany table p right).links (appendMany table p right).requests i := by
    have hm (a) : Satisfies table (appendMany table p left) a ↔
        Satisfies table (appendMany table p right) a := by
      rw [← solve_models_exact, ← solve_models_exact]
      exact update_order_models table p left right same a
    exact ⟨fun h a ha => h a ((hm a).mpr ha), fun h a ha => h a ((hm a).mp ha)⟩
  rw [solve_residual_exact, solve_residual_exact, hr, hf]

/-- Residual serialization uses one fixed slot-pair enumeration. Consequently
membership equality suffices for list equality within this representation;
duplicate names keep their distinct slot pairs, not duplicate request entries. -/
theorem residual_ext (table : Table) (p q : Problem table)
    (same : ∀ i j, (i,j) ∈ CommonRoleDynamicIndexResidualSource.residual table
      p.seeds p.links p.requests ↔
      (i,j) ∈ CommonRoleDynamicIndexResidualSource.residual table q.seeds q.links q.requests) :
    CommonRoleDynamicIndexResidualSource.residual table p.seeds p.links p.requests =
      CommonRoleDynamicIndexResidualSource.residual table q.seeds q.links q.requests := by
  unfold CommonRoleDynamicIndexResidualSource.residual CommonRoleDynamicIndexResidualSource.pairs
  simp only [List.filter_flatMap, List.filter_filterMap]
  apply congrArg (fun f => (List.finRange table.length).flatMap f)
  funext i
  apply congrArg (fun f => (List.finRange table.length).filterMap f)
  funext j
  have h := same i j
  simp only [CommonRoleDynamicIndexResidualSource.residual_exact,
    ← CommonRoleDynamicIndexEqualitySource.saturate_exact] at h
  by_cases hp : (source table i, source table j) ∈ p.requests <;>
    by_cases hq : (source table i, source table j) ∈ q.requests <;>
    by_cases sp : i ∈ CommonRoleDynamicIndexEqualitySource.saturate table p.seeds p.links p.requests <;>
    by_cases sq : i ∈ CommonRoleDynamicIndexEqualitySource.saturate table q.seeds q.links q.requests <;>
    simp_all [Option.filter]

/-- Finite incremental compaction returns the exact same pending list as a full
rebuild from all original batches, including its canonical slot-pair order.
The ordinary atom lists need not agree. -/
theorem solve_pending_rebuild (table : Table) (p : Problem table)
    (updates : List (Problem table)) :
    (solve table p updates).pending =
      (CommonRoleDynamicIndexResidualSource.build table
        (appendMany table p updates).seeds (appendMany table p updates).links
        (appendMany table p updates).requests).pending := by
  apply residual_ext table (advanceMany table p updates) (appendMany table p updates)
  intro i j
  change (i,j) ∈ (solve table p updates).pending ↔ _
  rw [solve_residual_exact, CommonRoleDynamicIndexResidualSource.residual_exact,
    ← CommonRoleDynamicIndexSourceSemantics.source_forces_iff]

/-- Permuting update batches preserves the entire serialized residual list.
This concerns the internal positive-string frontier, not final dictionaries. -/
theorem update_order_pending_list (table : Table) (p : Problem table)
    (left right : List (Problem table)) (same : ∀ u, u ∈ left ↔ u ∈ right) :
    (solve table p left).pending = (solve table p right).pending := by
  apply residual_ext table (advanceMany table p left) (advanceMany table p right)
  exact update_order_pending table p left right same

/-- The successful entrance exposes exactly the original full-rebuild frontier,
without requiring the caller to supply an independent model or closure proof. -/
theorem run_pending_rebuild (table : Table) (p : Problem table)
    (updates : List (Problem table)) (packet : Packet table)
    (h : run table p updates = .ok packet) :
    packet.pending =
      (CommonRoleDynamicIndexResidualSource.build table
        (appendMany table p updates).seeds (appendMany table p updates).links
        (appendMany table p updates).requests).pending := by
  rw [((run_ok_iff ..).mp h).2]
  exact solve_pending_rebuild ..

/-- Aliased discharged requests disappear while an unseeded cycle remains;
a late seed then closes precisely that residual cycle. -/
theorem aliased_cycle_frontier :
    let p : Problem [10,10,20,30,40] := ⟨[0], [], [(10,20),(30,40),(40,30)]⟩
    let update : Problem [10,10,20,30,40] := ⟨[], [(0,1)], [(20,10)]⟩
    let late : Problem [10,10,20,30,40] := ⟨[3], [], []⟩
    (solve [10,10,20,30,40] p [update]).pending = [(3,4),(4,3)] ∧
    (solve [10,10,20,30,40] p [update,late]).pending = [] := by
  decide

end Yulang.CommonRoleDynamicIndexResidualFrontier
