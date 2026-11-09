import Yulang.CommonRoleScalarSourceInspection
import Yulang.CommonRoleSourceDescent

/-! Canonical graph references for original source aliases, including unresolved
ones. Storage remains occurrence-sized; externally used roots share one finite
node exactly when their source names agree. Distinct names are never identified
just because their observations coincide. This flat positive-string adapter does
not construct recursive graphs or prove general role classification. -/
namespace Yulang.CommonRoleCanonicalSourceGraph
open CommonRoleSourceIdentity (Table Slot source)
open CommonRoleSourceDescent (representative representative_source representative_exists)
open CommonRoleDynamicIndexResidualBatches
open CommonRoleDynamicIndexSourceSemantics (ForcesString)
open CommonRoleScalarSourceInspection (graph code)
open CommonRoleGraphInspection (inspect inspectSnapshot VisibleHead)
open CommonRoleRegularGraph (Graph)
open Core.PresenceGeneration (Comp)

/-- Executable first occurrence. The default branch is unreachable for a slot. -/
def canonical (table : Table) (i : Slot table) : Slot table :=
  (representative table (source table i)).getD i

theorem canonical_source (table : Table) (i : Slot table) :
    source table (canonical table i) = source table i := by
  obtain ⟨first,h⟩ := representative_exists table i
  simpa only [canonical,h,Option.getD_some] using representative_source table _ first h

/-- The identity criterion is independent of scalar knowledge and of all models. -/
theorem canonical_eq_iff (table : Table) (i j : Slot table) :
    canonical table i = canonical table j ↔ source table i = source table j := by
  constructor
  · intro h
    exact (canonical_source table i).symm.trans
      ((congrArg (source table) h).trans (canonical_source table j))
  · intro h
    obtain ⟨first,found⟩ := representative_exists table i
    simp only [canonical, ← h, found, Option.getD_some]

theorem canonical_idempotent (table : Table) (i : Slot table) :
    canonical table (canonical table i) = canonical table i :=
  (canonical_eq_iff ..).mpr (canonical_source ..)

/-- The graph and its root map are produced together; no external graph is assumed. -/
structure Prepared (table : Table) where
  nodes : Graph table.length
  root : Slot table → Slot table

def prepare (table : Table) (p : Problem table) (updates : List (Problem table)) :
    Prepared table := ⟨graph (solve table p updates).state, canonical table⟩

theorem root_identity_exact (table : Table) (p : Problem table)
    (updates : List (Problem table)) (i j : Slot table) :
    (prepare table p updates).root i = (prepare table p updates).root j ↔
      source table i = source table j := canonical_eq_iff table i j

/-- Transport uses the independent original model's alias clause, not detection. -/
theorem forces_alias_iff (table : Table) (p : Problem table) (i j : Slot table)
    (same : source table i = source table j) :
    ForcesString table p.seeds p.links p.requests i ↔
      ForcesString table p.seeds p.links p.requests j := by
  constructor
  · intro h a ha
    exact Common.equivalent_trans (Common.equivalent_symm (ha.aliases i j same)) (h a ha)
  · intro h a ha
    exact Common.equivalent_trans (ha.aliases i j same) (h a ha)

/-- Soundness and completeness at the original occurrence, after canonical graph
routing. All finite batches, cycles, aliases and absent request names are allowed. -/
theorem inspect_string_exact (table : Table) (p : Problem table)
    (updates : List (Problem table)) (i : Slot table) :
    inspect (prepare table p updates).nodes (.scalar (code .str))
      ((prepare table p updates).root i) = .matched [] ↔
      ForcesString table (appendMany table p updates).seeds
        (appendMany table p updates).links (appendMany table p updates).requests i := by
  change inspect (graph (solve table p updates).state) (.scalar (code .str))
    (canonical table i) = .matched [] ↔ _
  rw [CommonRoleScalarSourceInspection.solve_inspect_string_exact]
  exact forces_alias_iff table (appendMany table p updates) _ _ (canonical_source table i)

/-- The existing inspector's unknown result is genuine original-source
underdetermination, with no caller-supplied consistency or scope-success premise. -/
theorem snapshot_unknown_exact (table : Table) (p : Problem table)
    (updates : List (Problem table)) (role : Nat) (i : Slot table)
    (visible : List VisibleHead) :
    inspectSnapshot (prepare table p updates).nodes role
      ((prepare table p updates).root i) visible = .unknown ↔
      ∃ a b : Slot table → Comp Common.model,
        Satisfies table (appendMany table p updates) a ∧
        Satisfies table (appendMany table p updates) b ∧
        ¬ Common.Equivalent (a i).1 (b i).1 := by
  change inspectSnapshot (graph (solve table p updates).state) role
    (canonical table i) visible = .unknown ↔ _
  rw [CommonRoleScalarSourceInspection.solve_snapshot_unknown_exact]
  change (∃ a b, CommonRoleDynamicIndexSourceSemantics.SourceModel table _ _ _ a ∧
    CommonRoleDynamicIndexSourceSemantics.SourceModel table _ _ _ b ∧ _) ↔
    (∃ a b, CommonRoleDynamicIndexSourceSemantics.SourceModel table _ _ _ a ∧
    CommonRoleDynamicIndexSourceSemantics.SourceModel table _ _ _ b ∧ _)
  rw [CommonRoleDynamicIndexSourceSemantics.source_underdetermined_iff,
    CommonRoleDynamicIndexSourceSemantics.source_underdetermined_iff]
  exact not_congr (forces_alias_iff table (appendMany table p updates)
    _ _ (canonical_source table i))

/-- Canonical routing does not alter the actual producer's success condition. -/
theorem checked_inspection_exact (table : Table) (p : Problem table)
    (updates : List (Problem table)) (i j : Slot table) :
    (∃ out, CommonRoleOrdinaryKnownness.checkedProduceIndex
      (solve table p updates).state i j = some out) ↔
      inspect (prepare table p updates).nodes (.scalar (code .str))
        ((prepare table p updates).root i) = .matched [] := by
  rw [inspect_string_exact]
  exact solve_checked_exact ..

/-- Original occurrence leaves keep their own indices and names while the graph
uses canonical references. The request membership premise preserves original scope. -/
theorem diagnostic_snapshot_exact (table : Table) (p : Problem table)
    (updates : List (Problem table)) (r : Nat × Nat)
    (hr : r ∈ (appendMany table p updates).requests) (role : Nat)
    (visible : List VisibleHead) (i j : Slot table) :
    ((i,j),true) ∈ (CommonRoleDynamicIndexOccurrenceDiagnostics.inspect table
      (solve table p updates) r).endpoints ↔
      source table i = r.1 ∧ source table j = r.2 ∧
      inspectSnapshot (prepare table p updates).nodes role
        ((prepare table p updates).root i) visible = .unknown := by
  rw [CommonRoleScalarSourceInspection.original_diagnostic_snapshot
    table p updates r hr role visible i j,
    CommonRoleScalarSourceInspection.solve_snapshot_unknown_exact,
    snapshot_unknown_exact]

/-- Equal observations are not used as identity. These three unresolved slots
have two distinct canonical roots, with exactly the named aliases sharing. -/
theorem unresolved_alias_regression :
    canonical [7,7,9] ⟨0,by decide⟩ = canonical [7,7,9] ⟨1,by decide⟩ ∧
    canonical [7,7,9] ⟨0,by decide⟩ ≠ canonical [7,7,9] ⟨2,by decide⟩ ∧
    (∀ i : Slot [7,7,9], graph CommonRoleSettledConstraints.State.empty
      (canonical [7,7,9] i) = .unresolved) := by
  refine ⟨by decide, by decide, ?_⟩
  intro i
  rfl


/-- Every computed scalar in this source fragment is string; other ordinary
scalars remain supported by the underlying graph adapter, not by this producer. -/
theorem solve_detected_base_str (table : Table) (p : Problem table)
    (updates : List (Problem table)) (i : Slot table) (b : Inference.Base)
    (h : CommonRoleOrdinaryKnownness.detect (solve table p updates).state.atoms i = some b) :
    b = .str :=
  CommonRoleDynamicIndexSemanticSource.detected_base_str table
    (advanceMany table p updates).seeds (advanceMany table p updates).links
    (advanceMany table p updates).requests i b h

/-- Canonicalizing an alias preserves the entire scalar reader, not only its
positive string bit. This uses the constructed source fragment explicitly. -/
theorem detect_alias_eq (table : Table) (p : Problem table)
    (updates : List (Problem table)) (i j : Slot table)
    (same : source table i = source table j) :
    CommonRoleOrdinaryKnownness.detect (solve table p updates).state.atoms i =
      CommonRoleOrdinaryKnownness.detect (solve table p updates).state.atoms j := by
  have str (k : Slot table) :
      CommonRoleOrdinaryKnownness.detect (solve table p updates).state.atoms k = some .str ↔
        ForcesString table (appendMany table p updates).seeds
          (appendMany table p updates).links (appendMany table p updates).requests k := by
    rw [← CommonRoleScalarSourceEndpoint.observe_detect,
      CommonRoleScalarSourceEndpoint.solve_string_exact]
  have equivalent := forces_alias_iff table (appendMany table p updates) i j same
  cases hi : CommonRoleOrdinaryKnownness.detect (solve table p updates).state.atoms i with
  | some b =>
    have hb := solve_detected_base_str table p updates i b hi
    subst b
    exact ((str j).mpr (equivalent.mp ((str i).mp hi))).symm
  | none =>
    cases hj : CommonRoleOrdinaryKnownness.detect (solve table p updates).state.atoms j with
    | none => rfl
    | some b =>
      have hb := solve_detected_base_str table p updates j b hj
      subst b
      have bad := (str i).mpr (equivalent.mpr ((str j).mp hj))
      rw [hi] at bad
      cases bad

theorem canonical_node_preserved (table : Table) (p : Problem table)
    (updates : List (Problem table)) (i : Slot table) :
    (prepare table p updates).nodes ((prepare table p updates).root i) =
      graph (solve table p updates).state i := by
  change graph (solve table p updates).state (canonical table i) = _
  simp only [graph, detect_alias_eq table p updates (canonical table i) i
    (canonical_source table i)]

/-- Route capture references as well as cycle references. The flat adapter
cannot produce cycles, but mapping that constructor keeps this operation total. -/
def route (table : Table) : CommonRoleGraphInspection.Observation table.length →
    CommonRoleGraphInspection.Observation table.length
  | .matched captures => .matched (captures.map fun c => (c.1,canonical table c.2))
  | .mismatch => .mismatch
  | .unresolved => .unresolved
  | .cycle i => .cycle (canonical table i)

/-- Every existing pattern inspection is preserved exactly after routing all
captured identities. This includes variable/shared captures at unknown nodes;
those captures are not silently compared as literal old occurrence indices. -/
theorem inspect_routing_exact (table : Table) (p : Problem table)
    (updates : List (Problem table)) (pattern : CommonRoleGraphInspection.Pattern)
    (i : Slot table) :
    inspect (prepare table p updates).nodes pattern ((prepare table p updates).root i) =
      route table (inspect (graph (solve table p updates).state) pattern i) := by
  have same := canonical_node_preserved table p updates i
  change graph (solve table p updates).state (canonical table i) = _ at same
  change inspect (graph (solve table p updates).state) pattern (canonical table i) = _
  cases pattern with
  | «variable» name => simp [inspect,route]
  | shared names => simp [inspect,route,List.map_map]
  | scalar name =>
    simp only [inspect, CommonRoleGraphBisimulation.regularAt, same]
    cases h : CommonRoleOrdinaryKnownness.detect (solve table p updates).state.atoms i <;>
      simp [graph,h,route] <;> split <;> rfl
  | structural name children =>
    simp only [inspect, CommonRoleGraphBisimulation.regularAt, same]
    cases h : CommonRoleOrdinaryKnownness.detect (solve table p updates).state.atoms i <;>
      simp [graph,h,route]
  | nominal name children =>
    simp only [inspect, CommonRoleGraphBisimulation.regularAt, same]
    cases h : CommonRoleOrdinaryKnownness.detect (solve table p updates).state.atoms i <;>
      simp [graph,h,route]

/-- Equal captured references mean equal source names even for unknown roots.
This is stronger than equal readout values and requires no source model premise. -/
theorem variable_capture_identity (table : Table) (p : Problem table)
    (updates : List (Problem table)) (name : Nat) (i j : Slot table) :
    inspect (prepare table p updates).nodes (.variable name) ((prepare table p updates).root i) =
      inspect (prepare table p updates).nodes (.variable name) ((prepare table p updates).root j) ↔
      source table i = source table j := by
  simp only [inspect, CommonRoleGraphInspection.Observation.matched.injEq,
    List.cons.injEq, Prod.mk.injEq, true_and, and_true]
  exact root_identity_exact ..

/-- Routing captures preserves their meaning in every independent original source
model. Only type equivalence is asserted; effect components are not equated. -/
theorem capture_type_sound (table : Table) (p : Problem table)
    (updates : List (Problem table)) (i : Slot table)
    (a : Slot table → Comp Common.model)
    (ha : Satisfies table (appendMany table p updates) a) :
    Common.Equivalent (a ((prepare table p updates).root i)).1 (a i).1 :=
  ha.aliases _ _ (canonical_source table i)

/-- End-to-end executable regression: an initially unknown alias pair captures
one root, and a seed arriving at the second occurrence wakes the original receiver
and its named target through the incremental source driver. -/
theorem shared_receiver_resume_regression :
    let p : Problem [7,7,9] := ⟨[],[],[(7,9)]⟩
    let update : Problem [7,7,9] := ⟨[1],[],[]⟩
    inspect (prepare [7,7,9] p []).nodes (.variable 4)
      ((prepare [7,7,9] p []).root 1) = .matched [(4,0)] ∧
    inspectSnapshot (prepare [7,7,9] p []).nodes 0
      ((prepare [7,7,9] p []).root 0) [] = .unknown ∧
    inspect (prepare [7,7,9] p [update]).nodes (.scalar (code .str))
      ((prepare [7,7,9] p [update]).root 0) = .matched [] ∧
    inspect (prepare [7,7,9] p [update]).nodes (.scalar (code .str))
      ((prepare [7,7,9] p [update]).root 2) = .matched [] := by
  decide +kernel

end Yulang.CommonRoleCanonicalSourceGraph
