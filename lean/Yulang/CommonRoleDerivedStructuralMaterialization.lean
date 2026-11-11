import Yulang.CommonRoleStructuralFrontierReplay
import Yulang.CommonRoleStructuralStateGrammar

/-! Materialization from actual finite structural derivations, including
transitive source-variable flow. Closure is computed from input syntax and
preserves every original model. Completeness is for the existing seed/split/trans
rules, not all Common subtype consequences or general role saturation. -/
namespace Yulang.CommonRoleDerivedStructuralMaterialization
open CommonRoleCaptureNormalization (Form)
open CommonRoleStructuralCarrierCoverage (Derives)
open CommonRoleFiniteStructuralClosure (normalize)
open CommonRoleStructuralOrdinaryMaterialization (decode Evidence)
open CommonRoleStructuralMaterializationProgress (Included Chain)
open CommonRoleStablePaterson (Declaration)
open CommonRoleIntervalPaterson (Goal)
open CommonRoleIntervalWorkClosure (Checked)
open CommonRoleGuardedIntervalPlans (Sources Plan)
open CommonRoleSettledConstraints (State)
open Core.PresenceGeneration (TyTerm Comp)
open PresenceNormalForm (Atom All)

/-- Independent paired structural derivation from the original seeds. Neither
normalization, materialization, ordinary solver nor candidate inspection occurs. -/
def DerivedEvidence (atoms : List (Atom (Fin n))) (slot : Fin n) (f : Form) : Prop :=
  (∃ t, Derives atoms (.tyLe (.var slot) t) ∧ decode t = some f) ∧
    ∃ t, Derives atoms (.tyLe t (.var slot)) ∧ decode t = some f

theorem evidence_exact (atoms : List (Atom (Fin n))) (slot : Fin n) (f : Form) :
    Evidence (normalize atoms) slot f ↔ DerivedEvidence atoms slot f := by
  simp only [Evidence,DerivedEvidence,CommonRoleStructuralCarrierCoverage.normalize_membership]

def detect (atoms : List (Atom (Fin n))) (slot : Fin n) : Option Form :=
  CommonRoleStructuralOrdinaryMaterialization.detect (normalize atoms) slot

/-- Soundness and completeness for a unique syntactic payload derivable by the
existing finite rules. Distinct equivalent syntax remains unresolved. -/
theorem detect_exact (atoms : List (Atom (Fin n))) (slot : Fin n) (f : Form) :
    detect atoms slot = some f ↔ DerivedEvidence atoms slot f ∧
      ∀ other, DerivedEvidence atoms slot other → other = f := by
  simp only [detect,CommonRoleStructuralOrdinaryMaterialization.detect_exact,evidence_exact]

theorem normalize_mono {before after : List (Atom (Fin n))} (included : Included before after) :
    Included (normalize before) (normalize after) := by
  intro atom member
  apply (CommonRoleStructuralCarrierCoverage.normalize_membership after atom).mpr
  exact CommonRoleStructuralCarrierCoverage.derives_cut (fun a h => .seed a (included a h))
    ((CommonRoleStructuralCarrierCoverage.normalize_membership before atom).mp member)

def materialize (atoms : List (Atom (Fin n))) (slots : Nat → Fin n) (f : Form) : Form :=
  CommonRoleStructuralOrdinaryMaterialization.materialize (normalize atoms) slots f

theorem materialize_meaning (atoms : List (Atom (Fin n))) (slots : Nat → Fin n)
    (v : Fin n → Comp Common.model) (models : All Common.model v atoms) (f : Form) :
    Common.Equivalent ((materialize atoms slots f).eval (fun k => (v (slots k)).1))
      (f.eval (fun k => (v (slots k)).1)) :=
  CommonRoleStructuralOrdinaryMaterialization.materialize_meaning (normalize atoms) slots v
    ((CommonRoleFiniteStructuralClosure.normalize_exact atoms v).mpr models) f

/-- Repeating the completed finite ordinary closure cannot create another
materialization change. This is not a stop rule for future incoming evidence. -/
theorem materialize_normalize (atoms : List (Atom (Fin n))) (slots : Nat → Fin n) (f : Form) :
    materialize (normalize atoms) slots f = materialize atoms slots f :=
  CommonRoleStructuralOrdinaryMaterialization.materialize_congr _ _
    (CommonRoleStructuralCarrierCoverage.normalize_idempotent atoms) slots f

theorem materialize_congr (before after : List (Atom (Fin n)))
    (same : ∀ atom, atom ∈ before ↔ atom ∈ after) (slots : Nat → Fin n) (f : Form) :
    materialize before slots f = materialize after slots f :=
  CommonRoleStructuralOrdinaryMaterialization.materialize_congr _ _
    (CommonRoleStructuralCarrierCoverage.normalize_congr before after same) slots f

theorem normalized_chain (initial : List (Atom (Fin n))) (states : List (List (Atom (Fin n))))
    (chain : Chain initial states) : Chain (normalize initial) (states.map normalize) := by
  induction states generalizing initial with
  | nil => trivial
  | cons next rest ih => exact ⟨normalize_mono chain.1,ih next chain.2⟩

abbrev normalizedTrace (initial : State n) (batches : List (State n)) :=
  (CommonRoleCheckedOrdinaryReplay.trace initial batches).map (fun state => normalize state.atoms)

theorem computed_chain (initial : State n) (batches : List (State n)) :
    Chain (normalize initial.atoms) (normalizedTrace initial batches) := by
  simpa only [List.map_map,Function.comp_def,normalizedTrace] using normalized_chain initial.atoms
    ((CommonRoleCheckedOrdinaryReplay.trace initial batches).map State.atoms)
    (CommonRoleStructuralMaterializationProgress.computed_chain initial batches)

theorem computed_covered (initial : State n) (batches : List (State n)) :
    ∀ atoms ∈ normalize initial.atoms :: normalizedTrace initial batches,
      Included atoms (normalize (CommonRoleCheckedOrdinaryReplay.final initial batches).atoms) := by
  intro atoms member
  rcases List.mem_cons.mp member with same | later
  · subst atoms; exact normalize_mono (CommonRoleCheckedOrdinaryReplay.final_includes initial batches)
  · obtain ⟨state,present,rfl⟩ := List.mem_map.mp later
    exact normalize_mono (CommonRoleStructuralMaterializationDomain.trace_includes_final initial batches state present)

/-- Validates original cumulative ordinary states, then computes finite closure
and complete structural replay. It takes no propagated state, trace, model,
proof of checking, finite carrier, or successful role assumption. -/
def run (registry : List Declaration) (slots : Nat → Fin n) (sources : Sources)
    (original : Goal) (initial : State n) (batches : List (State n)) :
    Option (CommonRoleStructuralFrontierReplay.Replay n) :=
  if CommonRoleCheckedOrdinaryReplay.validate initial batches then
    CommonRoleStructuralFrontierReplay.run registry slots sources original (normalize initial.atoms)
      (normalizedTrace initial batches)
  else none

theorem run_exact (registry : List Declaration) (slots : Nat → Fin n) (sources : Sources)
    (original : Goal) (initial : State n) (batches : List (State n))
    (output : CommonRoleStructuralFrontierReplay.Replay n) :
    run registry slots sources original initial batches = some output ↔
      (CommonRoleCheckedOrdinaryReplay.final initial batches).Models ∧ ∃ checked : Checked registry,
        output = CommonRoleStructuralFrontierReplay.replay registry checked slots sources original
          (normalize initial.atoms) (normalizedTrace initial batches) := by
  unfold run
  split
  · rename_i valid
    rw [CommonRoleStructuralFrontierReplay.run_exact]
    exact (and_iff_right ((CommonRoleCheckedOrdinaryReplay.validate_exact ..).mp valid)).symm
  · rename_i invalid
    constructor
    · intro impossible; cases impossible
    · rintro ⟨models,_⟩
      exact False.elim (invalid ((CommonRoleCheckedOrdinaryReplay.validate_exact ..).mpr models))

/-- The final computed closure supplies the finite child domain. Every snapshot
and failed branch is covered, with the same source-only rebuild factor. -/
theorem run_computed_bound (registry : List Declaration) (slots : Nat → Fin n) (sources : Sources)
    (original : Goal) (initial : State n) (batches : List (State n))
    (output : CommonRoleStructuralFrontierReplay.Replay n)
    (returned : run registry slots sources original initial batches = some output) :
    ∃ bound, CommonRoleStructuralMaterializationDomain.workDomain registry
        (normalize (CommonRoleCheckedOrdinaryReplay.final initial batches).atoms) slots original = some bound ∧
      output.snapshots.length = 1 + batches.length ∧
      output.rebuilds ≤ 1 + 2 * CommonRoleMaterializationProgress.potential original ∧
      output.visits ≤ (1 + 2 * CommonRoleMaterializationProgress.potential original) * bound.length ∧
      ∀ tree ∈ output.snapshots, ∀ target ∈ CommonRoleFrontierReachability.goals tree, target ∈ bound := by
  obtain ⟨_,checked,rfl⟩ := (run_exact ..).mp returned
  refine ⟨_,(CommonRoleStructuralMaterializationDomain.workDomain_exact ..).mpr ⟨checked,rfl⟩,?_,?_,?_,?_⟩
  · rw [CommonRoleStructuralFrontierReplay.replay_snapshots,List.length_map,List.length_cons,
      List.length_map,CommonRoleCheckedOrdinaryReplay.trace_length]
    omega
  · exact (CommonRoleStructuralFrontierReplay.replay_bounded registry checked slots sources original
      (normalize initial.atoms) _ _ (computed_chain initial batches) (computed_covered initial batches)).1
  · exact (CommonRoleStructuralFrontierReplay.replay_bounded registry checked slots sources original
      (normalize initial.atoms) _ _ (computed_chain initial batches) (computed_covered initial batches)).2
  · intro tree member target node
    exact CommonRoleStructuralFrontierReplay.replay_work_present registry checked slots sources original
      (normalize initial.atoms) _ _ (computed_covered initial batches) tree member target node

/-- Direct checked-state entry for all-model graph semantics. The graph compiler
retains original atoms through the finite closure; no consistency test discards
the graph before its model-existence statement is made. -/
def runState (registry : List Declaration) (slots : Nat → Fin n) (sources : Sources)
    (initial : State n) (old : Plan (Fin n)) (goal : Goal) :=
  CommonRoleStructuralOrdinaryMaterialization.run registry slots sources (normalize initial.atoms) old goal

/-- Every original assignment extends to an output graph exactly when it
satisfies the independent regenerated frontier and old demands. -/
theorem runState_models_exact (registry : List Declaration) (slots : Nat → Fin n) (sources : Sources)
    (initial : State n) (old : Plan (Fin n)) (goal : Goal) (assignment : Fin n → Comp Common.model) :
    (∃ output, runState registry slots sources initial old goal = some output ∧
      CommonRoleFrontierGraphs.Represents output.2 assignment) ↔
    Checked registry ∧ All Common.model assignment initial.atoms ∧ ∃ sourceValues,
      CommonRoleCaptureBatchModels.SharedFits assignment sourceValues old ∧
        CommonRoleGuardedIntervalPlans.Derives registry slots sources assignment sourceValues
          (CommonRoleStructuralOrdinaryMaterialization.materializeGoal (normalize initial.atoms) slots goal) := by
  change (∃ output, CommonRoleFrontierGraphs.run registry slots sources (normalize initial.atoms) old
      (CommonRoleStructuralOrdinaryMaterialization.materializeGoal (normalize initial.atoms) slots goal) = some output ∧
      CommonRoleFrontierGraphs.Represents output.2 assignment) ↔ _
  rw [CommonRoleFrontierGraphs.run_models_exact,CommonRoleFiniteStructuralClosure.normalize_exact]

/-- Reflection quantifies all graph realizers, not a selected solver witness. -/
theorem runState_graph_reflects (registry : List Declaration) (slots : Nat → Fin n) (sources : Sources)
    (initial : State n) (old : Plan (Fin n)) (goal : Goal) (output)
    (returned : runState registry slots sources initial old goal = some output)
    (graph : CommonPresenceConstraintGraph.Compiled n) (member : graph ∈ output.2)
    (rows : Fin n → Common.Row) (values : Fin graph.size → Common.Ty) (models : graph.Models rows values) :
    let v := graph.readback rows values
    All Common.model v initial.atoms ∧ ∀ f,
      Common.Equivalent ((materialize initial.atoms slots f).eval (fun k => (v (slots k)).1))
        (f.eval (fun k => (v (slots k)).1)) := by
  have reflected := CommonRoleStructuralOrdinaryMaterialization.run_graph_reflects registry slots sources
    (normalize initial.atoms) old goal output returned graph member rows values models
  exact ⟨(CommonRoleFiniteStructuralClosure.normalize_exact initial.atoms _).mp reflected.2.1,
    reflected.2.2.1⟩

end Yulang.CommonRoleDerivedStructuralMaterialization
