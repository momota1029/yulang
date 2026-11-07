import Yulang.CommonSignedChoiceDecision

/-! A finite symbolic row scheme with parameter-tested routing. The safety
check is computed before returning the scheme. Destination tests are finite
row Boolean operations, not a model or operation-local universal side
condition on parameters. Reachability denotes the regular symbolic closure.
With parameters equal to any original model, routing remains inside it. -/
namespace Yulang.CommonSignedChoiceSolver
open Common (Occurrence Row)
open CommonSignedChoicePreparation (Clause Graph Models Supported)
open CommonSignedChoiceDecision (check check_exact checked_successor)

structure Problem (n : Nat) where
  clauses : Graph n
  heads : List (Fin n × Occurrence)

def Problem.Models (problem : Problem n) (rows : Fin n → Row) : Prop :=
  CommonSignedChoicePreparation.Models problem.clauses rows ∧ ∀ seed ∈ problem.heads, rows seed.1 seed.2

def desired (graph : Graph n) (parameters : Fin n → Row) (clause : Clause n) (occurrence : Occurrence) : Prop :=
  ∃ slot ∈ clause.targets, check graph slot occurrence = true ∧ parameters slot occurrence

def chosen (graph : Graph n) (parameters : Fin n → Row) (clause : Clause n)
    (slot : Fin n) (occurrence : Occurrence) : Prop :=
  slot ∈ clause.targets ∧ check graph slot occurrence = true ∧
    (parameters slot occurrence ∨ ¬ desired graph parameters clause occurrence)

inductive Reach (graph : Graph n) (parameters : Fin n → Row) : Fin n → Occurrence → Fin n → Occurrence → Prop where
  | refl (slot : Fin n) (occurrence : Occurrence) : Reach graph parameters slot occurrence slot occurrence
  | next {start middle target : Fin n} {first source output : Occurrence} {clause : Clause n} :
      Reach graph parameters start first middle source → clause ∈ graph → clause.source = middle →
      clause.action.run source = some output → chosen graph parameters clause target output →
      Reach graph parameters start first target output

def instantiateRows (problem : Problem n) (parameters : Fin n → Row) : Fin n → Row :=
  fun slot occurrence => ∃ start first,
    check problem.clauses start first = true ∧
    (parameters start first ∨ (start, first) ∈ problem.heads) ∧
    Reach problem.clauses parameters start first slot occurrence

theorem reach_safe (graph : Graph n) (parameters : Fin n → Row) {start target : Fin n} {first last : Occurrence}
    (path : Reach graph parameters start first target last) (safe : check graph start first = true) :
    check graph target last = true := by
  cases path with
  | refl => exact safe
  | next _ _ _ _ selected => exact selected.2.1

theorem chosen_exists (graph : Graph n) (parameters : Fin n → Row) (clause : Clause n) (member : clause ∈ graph)
    (source target : Occurrence) (safe : check graph clause.source source = true)
    (runs : clause.action.run source = some target) : ∃ slot, chosen graph parameters clause slot target := by
  classical
  by_cases supported : desired graph parameters clause target
  · obtain ⟨slot, listed, safe, present⟩ := supported
    exact ⟨slot, listed, safe, Or.inl present⟩
  · obtain ⟨slot, listed, safe⟩ := checked_successor graph clause member source target safe runs
    exact ⟨slot, listed, safe, Or.inr supported⟩

theorem instantiate_clauses (problem : Problem n) (parameters : Fin n → Row) :
    Models problem.clauses (instantiateRows problem parameters) := by
  intro clause member source target present runs
  obtain ⟨start, first, safe, seed, path⟩ := present
  have sourceSafe := reach_safe problem.clauses parameters path safe
  obtain ⟨slot, selected⟩ := chosen_exists problem.clauses parameters clause member source target sourceSafe runs
  exact ⟨slot, selected.1, start, first, safe, seed, .next path member rfl runs selected⟩

def checkHeads (problem : Problem n) : Bool :=
  problem.heads.all (fun seed => check problem.clauses seed.1 seed.2)

theorem instantiate_models (problem : Problem n) (parameters : Fin n → Row) (valid : checkHeads problem = true) :
    problem.Models (instantiateRows problem parameters) := by
  refine ⟨instantiate_clauses problem parameters, ?_⟩
  intro seed member
  exact ⟨seed.1, seed.2, List.all_eq_true.mp valid seed member, Or.inr member, .refl _ _⟩

theorem models_checkHeads (problem : Problem n) (rows : Fin n → Row) (model : problem.Models rows) :
    checkHeads problem = true := by
  apply List.all_eq_true.mpr
  intro seed member
  exact (check_exact problem.clauses seed.1 seed.2).mpr ⟨rows, model.1, model.2 seed member⟩

theorem model_desired (graph : Graph n) (rows : Fin n → Row) (model : Models graph rows)
    (clause : Clause n) (member : clause ∈ graph) (source target : Occurrence)
    (present : rows clause.source source) (runs : clause.action.run source = some target) :
    desired graph rows clause target := by
  obtain ⟨slot, listed, next⟩ := model clause member source target present runs
  exact ⟨slot, listed, (check_exact graph slot target).mpr ⟨rows, model, next⟩, next⟩

theorem reach_stays (graph : Graph n) (rows : Fin n → Row) (model : Models graph rows)
    {start target : Fin n} {first last : Occurrence} (path : Reach graph rows start first target last)
    (seed : rows start first) : rows target last := by
  induction path with
  | refl => exact seed
  | @next middle target first source output clause path member same runs selected ih =>
    have present := ih seed
    have wanted := model_desired graph rows model clause member source output (same.symm ▸ present) runs
    exact selected.2.2.elim id (fun absent => False.elim (absent wanted))

theorem model_retraction (problem : Problem n) (rows : Fin n → Row) (model : problem.Models rows) :
    instantiateRows problem rows = rows := by
  funext slot occurrence
  apply propext
  constructor
  · rintro ⟨start, first, _, seed, path⟩
    exact reach_stays problem.clauses rows model.1 path (seed.elim id (model.2 (start, first)))
  · intro present
    exact ⟨slot, occurrence, (check_exact problem.clauses slot occurrence).mpr ⟨rows, model.1, present⟩,
      Or.inl present, .refl _ _⟩

def solve (problem : Problem n) : List (Problem n) := if checkHeads problem then [problem] else []

theorem mem_solve (problem scheme : Problem n) : scheme ∈ solve problem ↔ scheme = problem ∧ checkHeads problem = true := by
  cases checked : checkHeads problem <;> simp [solve, checked]

theorem all_parameters_models (problem scheme : Problem n) (returned : scheme ∈ solve problem) (parameters : Fin n → Row) :
    problem.Models (instantiateRows scheme parameters) := by
  obtain ⟨same, valid⟩ := (mem_solve problem scheme).mp returned
  subst scheme
  exact instantiate_models problem parameters valid

/-- Arbitrary independent rows, with literal recovery of every original slot;
no finite-row, support, fuel or universal parameter condition. -/
theorem solve_all_instances_exact (problem : Problem n) (rows : Fin n → Row) :
    problem.Models rows ↔ ∃ scheme ∈ solve problem, ∃ parameters : Fin n → Row, instantiateRows scheme parameters = rows := by
  constructor
  · intro model
    refine ⟨problem, (mem_solve problem problem).mpr ⟨rfl, models_checkHeads problem rows model⟩,
      rows, model_retraction problem rows model⟩
  · rintro ⟨scheme, returned, parameters, rfl⟩
    exact all_parameters_models problem scheme returned parameters

theorem rejected_iff (problem : Problem n) : solve problem = [] ↔ ¬ ∃ rows, problem.Models rows := by
  constructor
  · intro empty ⟨rows, model⟩
    have returned := (mem_solve problem problem).mpr ⟨rfl, models_checkHeads problem rows model⟩
    simp [empty] at returned
  · intro impossible
    cases checked : checkHeads problem with
    | false => simp [solve, checked]
    | true => exact False.elim (impossible ⟨_, instantiate_models problem (fun _ => Common.rowEmpty) checked⟩)
end Yulang.CommonSignedChoiceSolver
