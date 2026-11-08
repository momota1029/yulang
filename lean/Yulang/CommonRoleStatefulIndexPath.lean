import Yulang.CommonRoleStatefulIndexSweep

/-! A finite dependency path repeatedly materializes the last actual output.
Termination is structural on this explicit path, not general Paterson saturation. -/
namespace Yulang.CommonRoleStatefulIndexPath
open CommonRoleSettledConstraints (State)
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All)
open CommonRoleOrdinaryKnownness
open CommonRoleCandidateStateFrontier (extend)

def strAssignment : Fin n → Comp Common.model := fun _ => Comp.pure Common.model (.base .str)

theorem detect_of_str_evidence (s : State n) (slot : Fin n)
    (model : All Common.model strAssignment s.atoms)
    (evidence : Evidence s.atoms slot .str) : detect s.atoms slot = some .str := by
  obtain ⟨base, found⟩ := (detect_exists s.atoms slot).mpr ⟨.str, evidence⟩
  have same := evidence_unique s.atoms slot strAssignment model base .str
    (detect_evidence s.atoms slot base found) evidence
  simpa [same] using found

theorem extend_str_model (s : State n) (slot : Fin n)
    (model : All Common.model strAssignment s.atoms) :
    All Common.model strAssignment (extend s slot .str).atoms :=
  (CommonRoleCandidateStateFrontier.extend_exact ..).mpr ⟨model, Common.equivalent_refl _⟩

theorem extended_detected (s : State n) (slot : Fin n)
    (model : All Common.model strAssignment s.atoms) :
    detect (extend s slot .str).atoms slot = some .str := by
  apply detect_of_str_evidence _ _ (extend_str_model s slot model)
  constructor <;>
    simp [extend, CommonRoleCandidateStateFrontier.equality]

def run : List (Fin n) → Fin n → State n → Option (State n)
  | [], _, s => some s
  | output :: rest, receiver, s => do
      let next ← produceIndex s receiver output
      run rest output next

def expected : List (Fin n) → State n → State n
  | [], s => s
  | output :: rest, s => expected rest (extend s output .str)

theorem run_expected (outputs : List (Fin n)) (receiver : Fin n) (s : State n)
    (model : All Common.model strAssignment s.atoms)
    (known : detect s.atoms receiver = some .str) :
    run outputs receiver s = some (expected outputs s) := by
  induction outputs generalizing receiver s with
  | nil => rfl
  | cons output rest ih =>
    simp only [run, index_from_detected_str s receiver output known, expected]
    exact ih output _ (extend_str_model s output model) (extended_detected s output model)

theorem expected_models (outputs : List (Fin n)) (s : State n)
    (assignment : Fin n → Comp Common.model) :
    All Common.model assignment (expected outputs s).atoms ↔
      All Common.model assignment s.atoms ∧
      ∀ output ∈ outputs, Common.Equivalent (assignment output).1 (.base .str) := by
  induction outputs generalizing s with
  | nil => simp [expected]
  | cons output rest ih =>
    rw [expected, ih, CommonRoleCandidateStateFrontier.extend_exact]
    simp only [List.forall_mem_cons]
    exact and_assoc

/-- Re-running this already successful fixed path changes no models. -/
theorem expected_idempotent_models (outputs : List (Fin n)) (s : State n)
    (assignment : Fin n → Comp Common.model) :
    All Common.model assignment (expected outputs (expected outputs s)).atoms ↔
      All Common.model assignment (expected outputs s).atoms := by
  rw [expected_models, expected_models]
  exact and_self_right

/-- The seed is computed from the actual Index declaration, not supplied atoms. -/
def fromDeclaration (receiver : Fin n) (outputs : List (Fin n)) : Option (State n) := do
  let seed ← CommonRoleAssociatedStateFlow.fromSourceStore
    (Roles.AssocExamples.singletonEnv Roles.AssocExamples.boxImpl)
    Roles.AssocExamples.requiredRoles Roles.AssocExamples.box_paterson
    ⟨Roles.AssocExamples.index (Roles.AssocExamples.box Roles.Examples.str)
      Roles.Examples.int, 0, receiver⟩ State.empty
  run outputs receiver seed

theorem from_declaration_exact (receiver : Fin n) (outputs : List (Fin n)) :
    fromDeclaration receiver outputs =
      some (expected outputs (extend State.empty receiver .str)) := by
  unfold fromDeclaration
  rw [CommonRoleAssociatedStateFlow.source_store_agrees]
  let request : CommonRoleAssociatedStateFlow.Request n :=
    ⟨Roles.AssocExamples.index (Roles.AssocExamples.box Roles.Examples.str)
      Roles.Examples.int, 0, receiver⟩
  have computed : CommonRoleAssociatedStateFlow.Computed
      (Roles.AssocExamples.singletonEnv Roles.AssocExamples.boxImpl)
      Roles.AssocExamples.requiredRoles Roles.AssocExamples.box_paterson request .str :=
    ⟨rfl, _, Roles.AssocExamples.box_value, rfl⟩
  have result := (CommonRoleAssociatedStateFlow.value_exact ..).mpr computed
  change (CommonRoleAssociatedStateFlow.produce _ _ _ request State.empty).bind _ = _
  simp only [CommonRoleAssociatedStateFlow.produce, result, Option.map_some, Option.bind_some]
  exact run_expected outputs receiver _
    (extend_str_model State.empty receiver (PresenceNormalForm.all_nil _ _))
    (explicit_pair_detected receiver .str)

end Yulang.CommonRoleStatefulIndexPath
