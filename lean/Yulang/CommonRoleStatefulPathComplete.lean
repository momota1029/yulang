import Yulang.CommonRoleStatefulIndexPath

/-! Exact success domain for arbitrary old states and a finite dynamic path.
The length of the given dependency path supplies termination; no general
Paterson/K2 saturation statement is claimed. -/
namespace Yulang.CommonRoleStatefulPathComplete
open CommonRoleStatefulIndexPath
open CommonRoleSettledConstraints (State)
open CommonRoleOrdinaryKnownness
open CommonRoleCandidateStateFrontier (extend)
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All)

theorem detect_of_models (s : State n) (slot : Fin n) (models : s.Models)
    (evidence : Evidence s.atoms slot .str) : detect s.atoms slot = some .str := by
  obtain ⟨assignment, model⟩ := models
  obtain ⟨base, found⟩ := (detect_exists s.atoms slot).mpr ⟨.str, evidence⟩
  have same := evidence_unique s.atoms slot assignment model base .str
    (detect_evidence s.atoms slot base found) evidence
  simpa [same] using found

theorem extension_evidence (s : State n) (slot : Fin n) :
    Evidence (extend s slot .str).atoms slot .str := by
  constructor <;> simp [extend, CommonRoleCandidateStateFrontier.equality]

theorem path_preserves (outputs : List (Fin n)) (receiver : Fin n) (s out : State n)
    (result : run outputs receiver s = some out)
    (assignment : Fin n → Comp Common.model)
    (model : All Common.model assignment out.atoms) :
    All Common.model assignment s.atoms := by
  induction outputs generalizing receiver s with
  | nil => cases result; exact model
  | cons output rest ih =>
    cases produced : produceIndex s receiver output with
    | none => simp [run, produced] at result
    | some next =>
      simp only [run, produced] at result
      exact index_preserves s next receiver output produced assignment (ih output next result)

theorem run_expected_of_models (outputs : List (Fin n)) (receiver : Fin n) (s : State n)
    (models : (expected outputs s).Models)
    (evidence : Evidence s.atoms receiver .str) :
    run outputs receiver s = some (expected outputs s) := by
  induction outputs generalizing receiver s with
  | nil => rfl
  | cons output rest ih =>
    obtain ⟨assignment, model⟩ := models
    have old := ((expected_models (output :: rest) s assignment).mp model).1
    have known := detect_of_models s receiver ⟨assignment, old⟩ evidence
    simp only [run, index_from_detected_str s receiver output known, expected]
    exact ih output (extend s output .str) ⟨assignment, model⟩ (extension_evidence s output)

theorem successful_state (outputs : List (Fin n)) (receiver : Fin n) (s out : State n)
    (result : run outputs receiver s = some out) (models : out.Models)
    (evidence : Evidence s.atoms receiver .str) : out = expected outputs s := by
  induction outputs generalizing receiver s with
  | nil => exact (Option.some.inj result).symm
  | cons output rest ih =>
    obtain ⟨assignment, model⟩ := models
    have old := path_preserves (output :: rest) receiver s out result assignment model
    have known := detect_of_models s receiver ⟨assignment, old⟩ evidence
    simp only [run, index_from_detected_str s receiver output known] at result
    exact ih output (extend s output .str) result (extension_evidence s output)

/-- Same actual source seed as IndexPath.fromDeclaration, with arbitrary old constraints. -/
def seed (receiver : Fin n) (s : State n) : Option (State n) :=
  CommonRoleAssociatedStateFlow.fromSourceStore
    (Roles.AssocExamples.singletonEnv Roles.AssocExamples.boxImpl)
    Roles.AssocExamples.requiredRoles Roles.AssocExamples.box_paterson
    ⟨Roles.AssocExamples.index (Roles.AssocExamples.box Roles.Examples.str)
      Roles.Examples.int, 0, receiver⟩ s

theorem seed_exact (receiver : Fin n) (s : State n) : seed receiver s = some (extend s receiver .str) := by
  unfold seed
  rw [CommonRoleAssociatedStateFlow.source_store_agrees]
  let request : CommonRoleAssociatedStateFlow.Request n :=
    ⟨Roles.AssocExamples.index (Roles.AssocExamples.box Roles.Examples.str)
      Roles.Examples.int, 0, receiver⟩
  have computed : CommonRoleAssociatedStateFlow.Computed
      (Roles.AssocExamples.singletonEnv Roles.AssocExamples.boxImpl)
      Roles.AssocExamples.requiredRoles Roles.AssocExamples.box_paterson request .str :=
    ⟨rfl, _, Roles.AssocExamples.box_value, rfl⟩
  have result := (CommonRoleAssociatedStateFlow.value_exact ..).mpr computed
  change CommonRoleAssociatedStateFlow.produce _ _ _ request s = _
  simp only [CommonRoleAssociatedStateFlow.produce, result, Option.map_some]
  rfl

def checkedRun (outputs : List (Fin n)) (receiver : Fin n) (s : State n) : Option (State n) := do
  let initial ← seed receiver s
  let final ← run outputs receiver initial
  if CommonRoleOpenPropagation.consistent final then some final else none

/-- Arbitrary old constraints, arbitrary finite output path, no success/model premise. -/
theorem checked_exact (outputs : List (Fin n)) (receiver : Fin n) (s out : State n) :
    checkedRun outputs receiver s = some out ↔
      out = expected outputs (extend s receiver .str) ∧ out.Models := by
  unfold checkedRun
  rw [seed_exact]
  change (run outputs receiver (extend s receiver .str)).bind
    (fun final => if CommonRoleOpenPropagation.consistent final then some final else none) = some out ↔ _
  cases result : run outputs receiver (extend s receiver .str) with
  | none =>
    simp only [Option.bind_none]
    constructor
    · intro impossible; cases impossible
    · rintro ⟨rfl, models⟩
      have yes := run_expected_of_models outputs receiver _ models (extension_evidence s receiver)
      rw [result] at yes
      cases yes
  | some final =>
    simp only [Option.bind_some]
    by_cases accepted : CommonRoleOpenPropagation.consistent final = true
    · have models := (CommonRoleOpenPropagation.consistent_exact final).mp accepted
      have state := successful_state outputs receiver _ final result models (extension_evidence s receiver)
      simp only [accepted, ↓reduceIte, Option.some.injEq]
      constructor
      · intro same; subst out; exact ⟨state, models⟩
      · rintro ⟨same, _⟩; exact state.trans same.symm
    · have rejected := Bool.eq_false_iff.mpr accepted
      simp only [rejected, Bool.false_eq_true, ↓reduceIte]
      constructor
      · intro impossible; cases impossible
      · rintro ⟨rfl, models⟩
        have yes := run_expected_of_models outputs receiver _ models (extension_evidence s receiver)
        rw [result] at yes
        have same := Option.some.inj yes
        subst final
        exact False.elim (accepted ((CommonRoleOpenPropagation.consistent_exact _).mpr models))

/-- All original effect/type constraints are retained; only listed source type equations are added. -/
theorem checked_models_exact (outputs : List (Fin n)) (receiver : Fin n) (s : State n) :
    (∃ out, checkedRun outputs receiver s = some out) ↔
      ∃ assignment : Fin n → Comp Common.model,
        All Common.model assignment s.atoms ∧
        Common.Equivalent (assignment receiver).1 (.base .str) ∧
        ∀ output ∈ outputs, Common.Equivalent (assignment output).1 (.base .str) := by
  constructor
  · rintro ⟨out, result⟩
    obtain ⟨rfl, assignment, model⟩ := (checked_exact ..).mp result
    obtain ⟨seedModel, all⟩ := (expected_models ..).mp model
    obtain ⟨old, initial⟩ := (CommonRoleCandidateStateFrontier.extend_exact ..).mp seedModel
    exact ⟨assignment, old, initial, all⟩
  · rintro ⟨assignment, old, initial, all⟩
    refine ⟨_, (checked_exact ..).mpr ⟨rfl, assignment, ?_⟩⟩
    exact (expected_models ..).mpr
      ⟨(CommonRoleCandidateStateFrontier.extend_exact ..).mpr ⟨old, initial⟩, all⟩

end Yulang.CommonRoleStatefulPathComplete
