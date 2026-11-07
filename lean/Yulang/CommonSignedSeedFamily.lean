import Yulang.CommonSignedFlowFamily

/-! Required constants and signed cycles. Empty upper bounds reduce to the
precise static condition `HeadsSafe`; no decidability of that condition is
claimed. Without pure sinks the actual solver returns one finite scheme and
its unrestricted parameters recover every original row model. -/
namespace Yulang.CommonSignedSeedFamily
open Common (Occurrence Row)
open CommonSignedFlowFamily (Graph Path Safe)

structure Scheme (n : Nat) where
  graph : Graph n
  heads : List (Fin n × Occurrence)
  deriving DecidableEq, Repr

def Models (scheme : Scheme n) (rows : Fin n → Row) : Prop :=
  CommonSignedFlowFamily.Models scheme.graph rows ∧ ∀ head ∈ scheme.heads, rows head.1 head.2

def HeadsSafe (scheme : Scheme n) : Prop :=
  ∀ head ∈ scheme.heads, Safe scheme.graph head.1 head.2

def forced (scheme : Scheme n) (target : Fin n) (occurrence : Occurrence) : Prop :=
  ∃ head ∈ scheme.heads, Path scheme.graph head.1 head.2 target occurrence

def Scheme.instantiate (scheme : Scheme n) (parameters : Fin n → Row) : Fin n → Row :=
  fun target => Common.rowJoin (forced scheme target)
    ((CommonSignedFlowFamily.Scheme.mk scheme.graph).instantiate parameters target)

/-- Exact remaining consistency condition, independent of all parameters. -/
theorem all_parameters_models (scheme : Scheme n) (safe : HeadsSafe scheme)
    (parameters : Fin n → Row) : Models scheme (scheme.instantiate parameters) := by
  have parameterModel := CommonSignedFlowFamily.all_parameters_models ⟨scheme.graph⟩ parameters
  constructor
  · constructor
    · intro edge member a b present runs
      rcases present with forced | parameter
      · obtain ⟨head, headMember, path⟩ := forced
        exact Or.inl ⟨head, headMember, path.append (.cons member runs (.nil _ _))⟩
      · exact Or.inr (parameterModel.1 edge member a b parameter runs)
    · intro sink pure occurrence present
      rcases present with forced | parameter
      · obtain ⟨head, headMember, path⟩ := forced
        exact safe head headMember sink occurrence path pure
      · exact parameterModel.2 sink pure occurrence parameter
  · intro head member
    exact Or.inl ⟨head, member, .nil _ _⟩

theorem models_heads_safe (scheme : Scheme n) (rows : Fin n → Row) (model : Models scheme rows) :
    HeadsSafe scheme := by
  intro head member
  exact CommonSignedFlowFamily.model_seed_safe model.1 _ _ (model.2 head member)

theorem model_retraction (scheme : Scheme n) (rows : Fin n → Row) (model : Models scheme rows) :
    scheme.instantiate rows = rows := by
  funext target
  apply Common.rowLe_antisymm
  · intro occurrence present
    rcases present with forced | parameter
    · obtain ⟨head, member, path⟩ := forced
      exact path.models model.1 (model.2 head member)
    · have same := CommonSignedFlowFamily.model_retraction scheme.graph rows model.1
      exact (congrFun (congrFun same target) occurrence).mp parameter
  · intro occurrence present
    apply Or.inr
    have same := CommonSignedFlowFamily.model_retraction scheme.graph rows model.1
    exact (congrFun (congrFun same target) occurrence).mpr present

/-- A parameter-free semantic characterization of the still missing decision
procedure: a conflict is exactly a head path ending at a pure sink. -/
theorem satisfiable_iff_heads_safe (scheme : Scheme n) :
    (∃ rows, Models scheme rows) ↔ HeadsSafe scheme :=
  ⟨fun ⟨rows, model⟩ => models_heads_safe scheme rows model,
    fun safe => ⟨scheme.instantiate (fun _ => Common.rowEmpty), all_parameters_models scheme safe _⟩⟩

theorem inconsistent_iff_head_path (scheme : Scheme n) :
    (¬ ∃ rows, Models scheme rows) ↔
      ∃ head ∈ scheme.heads, ∃ sink ∈ scheme.graph.pure, ∃ occurrence,
        Path scheme.graph head.1 head.2 sink occurrence := by
  classical
  rw [satisfiable_iff_heads_safe]
  simp only [HeadsSafe, Safe, Classical.not_forall, Classical.not_not]
  constructor
  · rintro ⟨head, member, sink, occurrence, path, pure⟩
    exact ⟨head, member, sink, pure, occurrence, path⟩
  · rintro ⟨head, member, sink, pure, occurrence, path⟩
    exact ⟨head, member, sink, occurrence, path, pure⟩

/-- Finite signed/residual graph with constants and no empty upper bounds. -/
structure Problem (n : Nat) where
  edges : List (CommonSignedFlowFamily.Edge n)
  heads : List (Fin n × Occurrence)
  deriving DecidableEq, Repr

def coalesce (problem : Problem n) : Scheme n := ⟨⟨problem.edges, []⟩, problem.heads⟩
def solve (problem : Problem n) : List (Scheme n) := [coalesce problem]

theorem coalesce_safe (problem : Problem n) : HeadsSafe (coalesce problem) := by
  intro head _ target _ _
  simp [coalesce]

theorem returned_all_parameters (problem : Problem n) (scheme : Scheme n)
    (returned : scheme ∈ solve problem) (parameters : Fin n → Row) :
    Models (coalesce problem) (scheme.instantiate parameters) := by
  have same : scheme = coalesce problem := by simpa [solve] using returned
  subst scheme
  exact all_parameters_models _ (coalesce_safe problem) parameters

theorem solve_all_instances_exact (problem : Problem n) (rows : Fin n → Row) :
    Models (coalesce problem) rows ↔ ∃ scheme ∈ solve problem, ∃ parameters : Fin n → Row,
      scheme.instantiate parameters = rows := by
  constructor
  · intro model
    exact ⟨coalesce problem, by simp [solve], rows, model_retraction _ _ model⟩
  · rintro ⟨scheme, returned, parameters, same⟩
    rw [← same]
    exact returned_all_parameters problem scheme returned parameters

namespace Examples

def growing : Problem 1 :=
  ⟨[⟨0, 0, .shift 0 (.only []) 1⟩], [(0, (7, [0]))]⟩

def point (n : Nat) : Occurrence := (7, [Int.ofNat n])

theorem growing_path (n : Nat) : Path (coalesce growing).graph 0 (point 0) 0 (point n) := by
  induction n with
  | zero => exact .nil _ _
  | succ n ih =>
    apply ih.append
    apply Path.cons (edge := ⟨0, 0, .shift 0 (.only []) 1⟩) (next := point (n + 1))
    · simp [coalesce, growing]
    · simp [CommonSignedFlowFamily.Action.run, CommonSignedRows.shiftOccurrence,
        CommonEffectRequestGeneration.Permission.allows, point]
    · exact .nil _ _

/-- Even empty parameters yield unbounded positive weights at the one slot. -/
theorem growing_all_weights (n : Nat) (parameters : Fin 1 → Row) :
    (coalesce growing).instantiate parameters 0 (point n) := by
  exact Or.inl ⟨(0, point 0), by simp [coalesce, growing, point], growing_path n⟩

/-- No finite occurrence list can be the row of a model of this one-node
problem. This is an obstruction to finite enumeration, not to B3 itself. -/
theorem growing_no_finite_model (occurrences : List Occurrence) :
    ¬ Models (coalesce growing) (fun _ occurrence => occurrence ∈ occurrences) := by
  intro model
  have every (n : Nat) : point n ∈ occurrences := by
    exact (growing_path n).models model.1 (model.2 (0, point 0) (by simp [coalesce, growing, point]))
  have maximum : ∃ bound : Nat, ∀ occurrence ∈ occurrences, ∀ n, occurrence = point n → n < bound := by
    clear model every
    induction occurrences with
    | nil => exact ⟨0, by simp⟩
    | cons head tail ih =>
      obtain ⟨bound, boundSpec⟩ := ih
      by_cases headPoint : ∃ n, head = point n
      · obtain ⟨k, headEq⟩ := headPoint
        refine ⟨max bound (k + 1), ?_⟩
        intro occurrence member n same
        rcases List.mem_cons.mp member with rfl | member
        · have equal : k = n := by
            have weights := congrArg (fun occurrence : Occurrence => occurrence.2) (headEq.symm.trans same)
            have equalInt : Int.ofNat k = Int.ofNat n := by simpa [point] using weights
            exact Int.ofNat.inj equalInt
          omega
        · have less := boundSpec occurrence member n same
          omega
      · refine ⟨bound, ?_⟩
        intro occurrence member n same
        rcases List.mem_cons.mp member with rfl | member
        · exact False.elim (headPoint ⟨n, same⟩)
        · exact boundSpec occurrence member n same
  obtain ⟨bound, boundSpec⟩ := maximum
  exact (Nat.lt_irrefl bound) (boundSpec (point bound) (every bound) bound rfl)
end Examples
end Yulang.CommonSignedSeedFamily
