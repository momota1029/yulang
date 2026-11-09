import Yulang.CommonRoleScalarSourceEndpoint

/-! Source ordinary scalar readout connected to the existing graph inspector.
The graph retains original occurrence indices. This flat scalar fragment does
not construct recursive graphs or canonicalize unknown aliases. Head inspection
is not whole-candidate applicability, a dictionary, or final classification. -/
namespace Yulang.CommonRoleScalarSourceInspection
open CommonRoleSettledConstraints (State)
open CommonRoleOrdinaryKnownness (detect Evidence)
open CommonRoleScalarSourceEndpoint (observe)
open CommonRoleRegularGraph (Graph Node)
open CommonRoleGraphInspection (inspect inspectSnapshot VisibleHead)
open CommonRoleSourceIdentity (Table Slot)
open CommonRoleDynamicIndexResidualBatches
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All)

/-- Internal graph labels are injective; int/str agree with the term encoder.
The bool/unit labels do not extend the separate first-order role producer. -/
def code : Inference.Base → Nat
  | .int => 0
  | .str => 1
  | .bool => 2
  | .unit => 3

theorem code_injective (a b : Inference.Base) : code a = code b ↔ a = b := by
  cases a <;> cases b <;> decide

/-- One graph node per actual source occurrence slot; no guessed scalar or
nominal surrogate is inserted for an unresolved ordinary slot. -/
def graph (s : State n) : Graph n := fun i =>
  match detect s.atoms i with
  | none => .unresolved
  | some b => .scalar (code b)

theorem graph_scalar_exact (s : State n) (i : Fin n) (b : Inference.Base) :
    graph s i = .scalar (code b) ↔ observe s i = .scalar b := by
  rw [CommonRoleScalarSourceEndpoint.observe_detect]
  cases h : detect s.atoms i <;> simp [graph,h,code_injective]

theorem graph_unknown_exact (s : State n) (i : Fin n) :
    graph s i = .unresolved ↔ observe s i = .unknown := by
  rw [CommonRoleScalarSourceEndpoint.observe_unknown]
  cases h : detect s.atoms i <;> simp [graph,h]

/-- The existing inspector sees each scalar with its actual identity. This
statement is unconditional because it concerns the syntactic readout only. -/
theorem inspect_scalar_exact (s : State n) (i : Fin n) (b : Inference.Base) :
    inspect (graph s) (.scalar (code b)) i = .matched [] ↔
      observe s i = .scalar b := by
  rw [CommonRoleScalarSourceEndpoint.observe_detect]
  cases h : detect s.atoms i <;>
    simp [inspect, CommonRoleGraphBisimulation.regularAt, graph, h, code_injective, eq_comm]

/-- General scalar evidence is sound and complete for actual head matching
under an explicit ordinary model, without an externally supplied graph. -/
theorem inspect_evidence_exact (s : State n) (a : Fin n → Comp Common.model)
    (models : All Common.model a s.atoms) (i : Fin n) (b : Inference.Base) :
    inspect (graph s) (.scalar (code b)) i = .matched [] ↔ Evidence s.atoms i b := by
  rw [inspect_scalar_exact, CommonRoleScalarSourceEndpoint.observe_exact s a models]

/-- Arbitrary visible heads use the same unknown snapshot precisely when no
scalar observation exists. The role and visible list cannot invent knownness. -/
theorem snapshot_unknown_exact (s : State n) (role : Nat) (i : Fin n)
    (visible : List VisibleHead) :
    inspectSnapshot (graph s) role i visible = .unknown ↔ observe s i = .unknown := by
  rw [CommonRoleGraphInspection.snapshot_unknown_exact, graph_unknown_exact]

/-- Independent original source meaning reaches the actual graph head inspector.
All finite update batches, aliases, cycles, and missing request names are allowed;
this statement does not require a successful scope check or supplied model. -/
theorem solve_inspect_string_exact (table : Table) (p : Problem table)
    (updates : List (Problem table)) (i : Slot table) :
    inspect (graph (solve table p updates).state) (.scalar (code .str)) i = .matched [] ↔
      CommonRoleDynamicIndexSourceSemantics.ForcesString table
        (appendMany table p updates).seeds (appendMany table p updates).links
        (appendMany table p updates).requests i := by
  rw [inspect_scalar_exact, CommonRoleScalarSourceEndpoint.solve_string_exact]

/-- Unknown graph snapshots have two actual original source countermodels,
not merely a missing syntactic witness, in this constructed finite fragment. -/
theorem solve_snapshot_unknown_exact (table : Table) (p : Problem table)
    (updates : List (Problem table)) (role : Nat) (i : Slot table)
    (visible : List VisibleHead) :
    inspectSnapshot (graph (solve table p updates).state) role i visible = .unknown ↔
      ∃ a b : Slot table → Comp Common.model,
        Satisfies table (appendMany table p updates) a ∧
        Satisfies table (appendMany table p updates) b ∧
        ¬ Common.Equivalent (a i).1 (b i).1 := by
  rw [snapshot_unknown_exact, CommonRoleScalarSourceEndpoint.solve_unknown_exact]

/-- The original occurrence diagnostic's waiting bit is exactly the existing
inspector's unknown snapshot. Original names and endpoint pairs remain visible. -/
theorem original_diagnostic_snapshot (table : Table) (p : Problem table)
    (updates : List (Problem table)) (r : Nat × Nat)
    (hr : r ∈ (appendMany table p updates).requests) (role : Nat)
    (visible : List VisibleHead) (i j : Slot table) :
    ((i,j),true) ∈ (CommonRoleDynamicIndexOccurrenceDiagnostics.inspect table
      (solve table p updates) r).endpoints ↔
      CommonRoleSourceIdentity.source table i = r.1 ∧
      CommonRoleSourceIdentity.source table j = r.2 ∧
      inspectSnapshot (graph (solve table p updates).state) role i visible = .unknown := by
  rw [CommonRoleScalarSourceEndpoint.diagnostic_waiting_iff table p updates r hr,
    snapshot_unknown_exact]

/-- Every existing scalar survives the entire ordinary-to-graph-to-inspector
path. This includes bool/unit without claiming their term producer support. -/
theorem recorded_scalar_inspected (i : Fin n) (b : Inference.Base) :
    inspect (graph (CommonRoleCandidateStateFrontier.extend State.empty i b))
      (.scalar (code b)) i = .matched [] := by
  apply (inspect_scalar_exact ..).mpr
  apply (CommonRoleScalarSourceEndpoint.observe_detect ..).mpr
  exact CommonRoleOrdinaryKnownness.explicit_pair_detected i b

end Yulang.CommonRoleScalarSourceInspection
