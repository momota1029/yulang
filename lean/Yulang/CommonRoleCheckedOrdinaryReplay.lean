import Yulang.CommonRoleFrontierReplay

/-! Actual ordinary-solver validation of cumulative additive batches. The input
batches carry the existing solver grammar, not models or Chain. Their finite
length and source derivation remain external; this is not a saturation driver.
No candidate-local equality is committed merely because a candidate is unique. -/
namespace Yulang.CommonRoleCheckedOrdinaryReplay
open CommonRoleSettledConstraints (State)
open CommonRoleStablePaterson (Declaration)
open CommonRoleIntervalPaterson (Goal)
open CommonRoleGuardedIntervalPlans (Sources Plan)
open CommonRoleMaterializationProgress (Chain Extension potential)
open CommonRoleFrontierReplay (Replay)
open CommonRoleOpenPropagation (consistent)
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All Atom)

/-- Add a grammar-checked batch, retaining its exact atoms and multiplicity. -/
def append (state batch : State n) : State n :=
  ⟨state.atoms ++ batch.atoms, state.child.append batch.child,
    state.width.append batch.width, state.rows.append batch.rows⟩

def final (initial : State n) : List (State n) → State n
  | [] => initial
  | batch :: rest => final (append initial batch) rest

/-- Post-update states, computed rather than supplied by the caller. -/
def trace (initial : State n) : List (State n) → List (State n)
  | [] => []
  | batch :: rest => append initial batch :: trace (append initial batch) rest

/-- The real ordinary solver checks the initial state and every update. -/
def validate (initial : State n) (batches : List (State n)) : Bool :=
  (initial :: trace initial batches).all consistent

theorem append_models (state batch : State n) (assignment : Fin n → Comp Common.model) :
    All Common.model assignment (append state batch).atoms ↔
      All Common.model assignment state.atoms ∧ All Common.model assignment batch.atoms :=
  PresenceNormalForm.all_append ..

/-- The complete submitted atom stream, including duplicates, is retained. -/
theorem final_atoms (initial : State n) (batches : List (State n)) :
    (final initial batches).atoms = initial.atoms ++ batches.flatMap State.atoms := by
  induction batches generalizing initial with
  | nil => simp [final]
  | cons batch rest ih => simp only [final,ih,append,List.flatMap_cons,List.append_assoc]

/-- A single shared assignment satisfies the initial state and every batch. -/
theorem final_models (initial : State n) (batches : List (State n))
    (assignment : Fin n → Comp Common.model) :
    All Common.model assignment (final initial batches).atoms ↔
      All Common.model assignment initial.atoms ∧
        ∀ batch ∈ batches, All Common.model assignment batch.atoms := by
  induction batches generalizing initial with
  | nil => simp [final]
  | cons batch rest ih =>
      rw [final,ih,append_models]
      simp only [List.forall_mem_cons]
      exact and_assoc

theorem final_includes (initial : State n) (batches : List (State n)) :
    ∀ atom ∈ initial.atoms, atom ∈ (final initial batches).atoms := by
  induction batches generalizing initial with
  | nil => exact fun _ h => h
  | cons batch rest ih =>
      intro atom member
      exact ih (append initial batch) atom (List.mem_append_left _ member)

theorem final_models_initial (initial : State n) (batches : List (State n))
    (models : (final initial batches).Models) : initial.Models := by
  obtain ⟨assignment,models⟩ := models
  exact ⟨assignment,fun atom member => models atom (final_includes initial batches atom member)⟩

/-- Exact satisfiability of all accumulated ordinary constraints. There is no
supplied model, preserved-consistency premise or role-success assumption. -/
theorem validate_exact (initial : State n) (batches : List (State n)) :
    validate initial batches = true ↔ (final initial batches).Models := by
  induction batches generalizing initial with
  | nil => simpa [validate,trace,final] using CommonRoleOpenPropagation.consistent_exact initial
  | cons batch rest ih =>
      change (consistent initial && validate (append initial batch) rest) = true ↔ _
      rw [Bool.and_eq_true_iff,CommonRoleOpenPropagation.consistent_exact,ih]
      constructor
      · exact fun pair => pair.2
      · intro models
        exact ⟨final_models_initial initial (batch :: rest) models,models⟩

/-- Independent conjunction of submitted constraints, with one assignment for
all batches. Individually feasible batches need not be jointly feasible. -/
theorem validate_models (initial : State n) (batches : List (State n)) :
    validate initial batches = true ↔
      ∃ assignment : Fin n → Comp Common.model,
        All Common.model assignment initial.atoms ∧
          ∀ batch ∈ batches, All Common.model assignment batch.atoms := by
  rw [validate_exact]
  exact exists_congr fun assignment => final_models initial batches assignment

theorem trace_length (initial : State n) (batches : List (State n)) :
    (trace initial batches).length = batches.length := by
  induction batches generalizing initial with
  | nil => rfl
  | cons batch rest ih => simp only [trace,List.length_cons,ih]

/-- Successful executable checking constructs the Chain premise used by the
materialization bound. The cumulative states are not a separate input. -/
theorem validate_chain (initial : State n) (batches : List (State n))
    (valid : validate initial batches = true) :
    Chain initial.atoms ((trace initial batches).map State.atoms) := by
  induction batches generalizing initial with
  | nil => trivial
  | cons batch rest ih =>
      have parts : consistent initial = true ∧ validate (append initial batch) rest = true :=
        Bool.and_eq_true_iff.mp valid
      have models := final_models_initial (append initial batch) rest
        ((validate_exact _ _).mp parts.2)
      exact ⟨⟨fun _ member => List.mem_append_left _ member,models⟩,ih _ parts.2⟩

/-- An ordinary-consistency gate followed by the existing declaration-checked
replay. The gate is executable, not a semantic oracle. -/
def run (registry : List Declaration) (slots : Nat → Fin n) (sources : Sources)
    (original : Goal) (initial : State n) (batches : List (State n)) : Option (Replay n) :=
  if validate initial batches then
    CommonRoleFrontierReplay.run registry slots sources original initial.atoms
      ((trace initial batches).map State.atoms)
  else none

/-- Exact success criterion: final accumulated ordinary models and the
independent checked-registry predicate. Invalid syntax is not unsatisfiability. -/
theorem run_exact (registry : List Declaration) (slots : Nat → Fin n) (sources : Sources)
    (original : Goal) (initial : State n) (batches : List (State n)) (output : Replay n) :
    run registry slots sources original initial batches = some output ↔
      (final initial batches).Models ∧
      ∃ checked : CommonRoleIntervalWorkClosure.Checked registry,
        output = CommonRoleFrontierReplay.replay registry checked slots sources original initial.atoms
          ((trace initial batches).map State.atoms) := by
  unfold run
  split
  · rename_i valid
    rw [CommonRoleFrontierReplay.run_exact]
    exact (and_iff_right ((validate_exact _ _).mp valid)).symm
  · rename_i invalid
    constructor
    · intro impossible; cases impossible
    · rintro ⟨models,_⟩
      exact False.elim (invalid ((validate_exact _ _).mpr models))

/-- Failure is exactly ordinary inconsistency or failed declaration checking.
This does not turn unresolved role children into ordinary contradictions. -/
theorem run_none_iff (registry : List Declaration) (slots : Nat → Fin n) (sources : Sources)
    (original : Goal) (initial : State n) (batches : List (State n)) :
    run registry slots sources original initial batches = none ↔
      ¬ (final initial batches).Models ∨ ¬ CommonRoleIntervalWorkClosure.Checked registry := by
  classical
  constructor
  · intro absent
    by_cases models : (final initial batches).Models
    · right
      intro checked
      have found := (run_exact registry slots sources original initial batches
        (CommonRoleFrontierReplay.replay registry checked slots sources original initial.atoms
          ((trace initial batches).map State.atoms))).mpr ⟨models,checked,rfl⟩
      rw [absent] at found
      cases found
    · exact Or.inl models
  · intro failed
    cases found : run registry slots sources original initial batches with
    | none => rfl
    | some output =>
        obtain ⟨models,checked,_⟩ := (run_exact ..).mp found
        exact False.elim (failed.elim (fun bad => bad models) (fun bad => bad checked))

/-- No caller Chain, model, checker proof or numerical bound is required.
The input batches are still finite and source derivation is not established. -/
theorem run_computed_bound (registry : List Declaration) (slots : Nat → Fin n) (sources : Sources)
    (original : Goal) (initial : State n) (batches : List (State n)) (output : Replay n)
    (returned : run registry slots sources original initial batches = some output) :
    ∃ bound, CommonRoleStateMaterializedFrontier.workDomain registry original = some bound ∧
      output.snapshots.length = 1 + batches.length ∧
      output.rebuilds ≤ 1 + potential original ∧
      output.visits ≤ (1 + potential original) * bound.length := by
  have exactResult := (run_exact ..).mp returned
  have valid := (validate_exact _ _).mpr exactResult.1
  have replay : CommonRoleFrontierReplay.run registry slots sources original initial.atoms
      ((trace initial batches).map State.atoms) = some output := by
    simpa only [run,valid,ite_true] using returned
  obtain ⟨bound,hbound,hlen,hrest⟩ := CommonRoleFrontierReplay.run_computed_bound
    registry slots sources original initial.atoms ((trace initial batches).map State.atoms)
      output replay (validate_chain initial batches valid)
  exact ⟨bound,hbound,by simpa only [List.length_map,trace_length] using hlen,hrest⟩

/-- Public graph-returning entry. No graph or snapshot is exposed before the
real ordinary consistency check; graphs themselves are not claimed satisfiable. -/
def runGraphs (registry : List Declaration) (slots : Nat → Fin n) (sources : Sources)
    (original : Goal) (initial : State n) (batches : List (State n))
    (old : Nat → Plan (Fin n)) :=
  if validate initial batches then
    CommonRoleFrontierReplay.runGraphs registry slots sources original initial.atoms
      ((trace initial batches).map State.atoms) old
  else none

/-- Cached diagnostics still feed freshly regenerated ordinary graphs at each
batch occurrence, with independently varying old demands on equal states. -/
theorem run_graphs_exact (registry : List Declaration) (slots : Nat → Fin n) (sources : Sources)
    (original : Goal) (initial : State n) (batches : List (State n)) (output : Replay n)
    (returned : run registry slots sources original initial batches = some output)
    (old : Nat → Plan (Fin n)) :
    ∃ graphs, runGraphs registry slots sources original initial batches old = some (output,graphs) ∧
      graphs.map some = (initial.atoms :: (trace initial batches).map State.atoms).mapIdx
        (fun i atoms => CommonRoleStateMaterializedFrontier.run registry slots sources atoms (old i) original) := by
  have valid := (validate_exact _ _).mpr ((run_exact ..).mp returned).1
  simp only [runGraphs,valid,ite_true]
  apply CommonRoleFrontierReplay.runGraphs_exact
  simpa only [run,valid,ite_true] using returned

end Yulang.CommonRoleCheckedOrdinaryReplay
