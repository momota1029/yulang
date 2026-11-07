import Yulang.CommonCaseOrderedPaths
import Yulang.Common

/-! Compositional effect bounds for the actual ordered case paths. Source
event rows and error rows are arbitrary interpretations. Both the rows of
the visited prefix and the conservative rows of every arm are sound upper
bounds when the corresponding real test/body observations are bounded.
This does not choose which bound source inference should expose. -/

namespace Yulang.CommonCaseEffectPaths

open CaseValues EvaluationTrace
open CaseEvaluation (Arm Event)
open Common (Row rowLe rowJoin rowEmpty)

def eventRow (source : E → Row) : Event E → Row
  | .source item => source item
  | _ => rowEmpty

def traceRow (source : E → Row) : List (Event E) → Row
  | [] => rowEmpty
  | first :: rest => rowJoin (eventRow source first) (traceRow source rest)

def resultRow (failure : R → Row) : Except R A → Row
  | .error error => failure error
  | .ok _ => rowEmpty

def observationRow (source : E → Row) (failure : R → Row) (observation : Logged (Event E) R A) : Row :=
  rowJoin (traceRow source observation.trace) (resultRow failure observation.result)

theorem traceRow_append (source : E → Row) (first last : List (Event E)) :
    traceRow source (first ++ last) = rowJoin (traceRow source first) (traceRow source last) := by
  induction first with
  | nil => funext occurrence; simp [traceRow, rowJoin, rowEmpty]
  | cons event rest ih => funext occurrence; simp [traceRow, ih, rowJoin, or_assoc]

theorem resultRow_map (failure : R → Row) (result : Except R A) (map : A → B) :
    resultRow failure (result.map map) = resultRow failure result := by cases result <;> rfl

theorem observationRow_arm (source : E → Row) (failure : R → Row) (index : Nat)
    (events : List (Event E)) (result : Except R A) :
    observationRow source failure ⟨.arm index :: events, result⟩ = observationRow source failure ⟨events, result⟩ := by
  funext occurrence
  simp [observationRow, traceRow, eventRow, rowJoin, rowEmpty]

theorem miss_row (source : E → Row) (failure : R → Row) (index : Nat)
    (events more : List (Event E)) (result : Except R A) :
    observationRow source failure ⟨.arm index :: (events ++ more), result⟩ =
      rowJoin (observationRow source failure (A := Option (Bindings F)) ⟨events, .ok none⟩)
        (observationRow source failure ⟨more, result⟩) := by
  funext occurrence
  simp [observationRow, traceRow, eventRow, traceRow_append, resultRow, rowJoin, rowEmpty, or_assoc]

theorem selected_row (source : E → Row) (failure : R → Row) (index : Nat) (events : List (Event E))
    (bindings : Bindings F) (body : Logged (Event E) R A) :
    observationRow source failure ⟨.arm index :: (events ++ .body index :: body.trace), body.result.map some⟩ =
      rowJoin (observationRow source failure ⟨events, .ok (some bindings)⟩) (observationRow source failure body) := by
  simp only [observationRow, resultRow_map]
  funext occurrence
  simp [traceRow, eventRow, traceRow_append, resultRow, rowJoin, rowEmpty, or_assoc]

private theorem le_join_left (first last : Row) : rowLe first (rowJoin first last) := fun _ => Or.inl
private theorem le_join_right (first last : Row) : rowLe last (rowJoin first last) := fun _ => Or.inr

variable (floatCheck : F → F → Bool)
  (defaultEval : Bindings F → D → Logged (Event E) R (Value F)) (environment : Bindings F)
  (guardEval : G → Bindings F → Logged (Event E) R Bool)
  (bodyEval : B → Bindings F → Logged (Event E) R (Value F))
  (declared : Nat → Arm F D G B → Row × Row)

def usedRows (value : Value F) (index : Nat) : List (Arm F D G B) → Row
  | [] => rowEmpty
  | arm :: rest =>
      match (ScopedCaseEvaluation.testArm floatCheck defaultEval environment guardEval index arm value).result with
      | .error _ => (declared index arm).1
      | .ok none => rowJoin (declared index arm).1 (usedRows value (index + 1) rest)
      | .ok (some _) => rowJoin (declared index arm).1 (declared index arm).2

def allRows (index : Nat) : List (Arm F D G B) → Row
  | [] => rowEmpty
  | arm :: rest => rowJoin (declared index arm).1 (rowJoin (declared index arm).2 (allRows (index + 1) rest))

theorem usedRows_le_allRows (value : Value F) (index : Nat) (arms : List (Arm F D G B)) :
    rowLe (usedRows floatCheck defaultEval environment guardEval declared value index arms) (allRows declared index arms) := by
  induction arms generalizing index with
  | nil => exact Common.rowLe_refl _
  | cons arm rest ih =>
      simp only [usedRows, allRows]
      cases (ScopedCaseEvaluation.testArm floatCheck defaultEval environment guardEval index arm value).result with
      | error => exact le_join_left _ _
      | ok option =>
          cases option with
          | none => exact (Common.rowJoin_le_iff _ _ _).mpr ⟨le_join_left _ _,
              Common.rowLe_trans (ih (index + 1)) (Common.rowLe_trans (le_join_right _ _) (le_join_right _ _))⟩
          | some => exact (Common.rowJoin_le_iff _ _ _).mpr ⟨le_join_left _ _,
              Common.rowLe_trans (le_join_left _ _) (le_join_right _ _)⟩

theorem path_bound (source : E → Row) (failure : R → Row)
    (path : CommonCaseOrderedPaths.RunPath floatCheck defaultEval environment guardEval bodyEval value index arms events result) :
    (∀ index arm, arm ∈ arms → rowLe
      (observationRow source failure (ScopedCaseEvaluation.testArm floatCheck defaultEval environment guardEval index arm value))
      (declared index arm).1) →
    (∀ index arm, arm ∈ arms → ∀ bindings,
      (ScopedCaseEvaluation.testArm floatCheck defaultEval environment guardEval index arm value).result = .ok (some bindings) →
      rowLe (observationRow source failure (bodyEval arm.body bindings)) (declared index arm).2) →
    rowLe (observationRow source failure ⟨events, result⟩)
      (usedRows floatCheck defaultEval environment guardEval declared value index arms) := by
  induction path with
  | nil =>
      intro tests bodies
      exact (Common.rowJoin_le_iff _ _ _).mpr ⟨Common.rowLe_refl _, Common.rowLe_refl _⟩
  | error tested =>
      rename_i index arm events error rest
      intro tests bodies
      have cap := tests index arm List.mem_cons_self
      rw [tested.observation] at cap
      rw [usedRows, congrArg Logged.result tested.observation, observationRow_arm]
      exact cap
  | miss tested later ih =>
      rename_i index arm events rest more result
      intro tests bodies
      have cap := tests index arm List.mem_cons_self
      rw [tested.observation] at cap
      have tail := ih (fun index arm member => tests index arm (List.mem_cons_of_mem _ member))
        (fun index arm member => bodies index arm (List.mem_cons_of_mem _ member))
      rw [usedRows, congrArg Logged.result tested.observation, miss_row source failure (F := F)]
      exact (Common.rowJoin_le_iff _ _ _).mpr
        ⟨Common.rowLe_trans cap (le_join_left _ _), Common.rowLe_trans tail (le_join_right _ _)⟩
  | selected tested =>
      rename_i index arm events bindings rest
      intro tests bodies
      have cap := tests index arm List.mem_cons_self
      rw [tested.observation] at cap
      have body := bodies index arm List.mem_cons_self bindings (congrArg Logged.result tested.observation)
      rw [usedRows, congrArg Logged.result tested.observation, selected_row source failure index events bindings]
      exact (Common.rowJoin_le_iff _ _ _).mpr
        ⟨Common.rowLe_trans cap (le_join_left _ _), Common.rowLe_trans body (le_join_right _ _)⟩

/-- Arbitrary real callbacks, including failures. Callback bounds are needed
only for actual test observations, and a body bound only after its real test
hit. Error rows and preceding effects are retained; later arms contribute
no row to usedRows. Source typing must separately establish these bounds. -/
theorem runArms_bound (source : E → Row) (failure : R → Row)
    (value : Value F) (index : Nat) (arms : List (Arm F D G B))
    (tests : ∀ index arm, arm ∈ arms → rowLe
      (observationRow source failure (ScopedCaseEvaluation.testArm floatCheck defaultEval environment guardEval index arm value))
      (declared index arm).1)
    (bodies : ∀ index arm, arm ∈ arms → ∀ bindings,
      (ScopedCaseEvaluation.testArm floatCheck defaultEval environment guardEval index arm value).result = .ok (some bindings) →
      rowLe (observationRow source failure (bodyEval arm.body bindings)) (declared index arm).2) :
    rowLe (observationRow source failure
      (ScopedCaseEvaluation.runArms floatCheck defaultEval environment guardEval bodyEval value index arms))
      (usedRows floatCheck defaultEval environment guardEval declared value index arms) :=
  path_bound floatCheck defaultEval environment guardEval bodyEval declared source failure
    (CommonCaseOrderedPaths.runPath_actual floatCheck defaultEval environment guardEval bodyEval value index arms) tests bodies

theorem runArms_static_bound (source : E → Row) (failure : R → Row)
    (value : Value F) (index : Nat) (arms : List (Arm F D G B))
    (tests : ∀ index arm, arm ∈ arms → rowLe
      (observationRow source failure (ScopedCaseEvaluation.testArm floatCheck defaultEval environment guardEval index arm value))
      (declared index arm).1)
    (bodies : ∀ index arm, arm ∈ arms → ∀ bindings,
      (ScopedCaseEvaluation.testArm floatCheck defaultEval environment guardEval index arm value).result = .ok (some bindings) →
      rowLe (observationRow source failure (bodyEval arm.body bindings)) (declared index arm).2) :
    rowLe (observationRow source failure
      (ScopedCaseEvaluation.runArms floatCheck defaultEval environment guardEval bodyEval value index arms))
      (allRows declared index arms) :=
  Common.rowLe_trans (runArms_bound floatCheck defaultEval environment guardEval bodyEval declared
    source failure value index arms tests bodies)
    (usedRows_le_allRows floatCheck defaultEval environment guardEval declared value index arms)

def usedCaseRows (subject : Logged (Event E) R (Value F)) (subjectRow : Row) (arms : List (Arm F D G B)) : Row :=
  match subject.result with
  | .error _ => subjectRow
  | .ok value => rowJoin subjectRow (usedRows floatCheck defaultEval environment guardEval declared value 0 arms)

theorem eval_observation_row (source : E → Row) (failure : R → Row)
    (subject : Logged (Event E) R (Value F)) (arms : List (Arm F D G B)) :
    observationRow source failure (ScopedCaseEvaluation.eval floatCheck defaultEval environment guardEval bodyEval subject arms) =
      match subject.result with
      | .error _ => observationRow source failure subject
      | .ok value => rowJoin (observationRow source failure subject)
          (observationRow source failure (ScopedCaseEvaluation.runArms floatCheck defaultEval environment guardEval bodyEval value 0 arms)) := by
  cases subject with
  | mk events result =>
      cases result <;> funext occurrence <;>
        simp [ScopedCaseEvaluation.eval, Logged.bind, Logged.prepend, observationRow, traceRow,
          eventRow, traceRow_append, resultRow, rowJoin, rowEmpty, or_assoc]

/-- Full subject-before-arms composition. A failing subject retains its own
failure row and contributes no arm row. All interpretations and callbacks
are arbitrary; the caller supplies actual source observation bounds. -/
theorem eval_bound (source : E → Row) (failure : R → Row)
    (subject : Logged (Event E) R (Value F)) (subjectRow : Row) (arms : List (Arm F D G B))
    (subjectBound : rowLe (observationRow source failure subject) subjectRow)
    (tests : ∀ value, subject.result = .ok value → ∀ index arm, arm ∈ arms → rowLe
      (observationRow source failure (ScopedCaseEvaluation.testArm floatCheck defaultEval environment guardEval index arm value))
      (declared index arm).1)
    (bodies : ∀ value, subject.result = .ok value → ∀ index arm, arm ∈ arms → ∀ bindings,
      (ScopedCaseEvaluation.testArm floatCheck defaultEval environment guardEval index arm value).result = .ok (some bindings) →
      rowLe (observationRow source failure (bodyEval arm.body bindings)) (declared index arm).2) :
    rowLe (observationRow source failure (ScopedCaseEvaluation.eval floatCheck defaultEval environment guardEval bodyEval subject arms))
      (usedCaseRows floatCheck defaultEval environment guardEval declared subject subjectRow arms) := by
  rw [eval_observation_row]
  cases observed : subject.result with
  | error => simpa only [usedCaseRows, observed] using subjectBound
  | ok value =>
      simp only [usedCaseRows, observed]
      exact (Common.rowJoin_le_iff _ _ _).mpr ⟨Common.rowLe_trans subjectBound (le_join_left _ _),
        Common.rowLe_trans (runArms_bound floatCheck defaultEval environment guardEval bodyEval declared
          source failure value 0 arms (tests value observed) (bodies value observed)) (le_join_right _ _)⟩

theorem usedCaseRows_le_static (subject : Logged (Event E) R (Value F)) (subjectRow : Row)
    (arms : List (Arm F D G B)) :
    rowLe (usedCaseRows floatCheck defaultEval environment guardEval declared subject subjectRow arms)
      (rowJoin subjectRow (allRows declared 0 arms)) := by
  cases observed : subject.result with
  | error => simpa only [usedCaseRows, observed] using le_join_left subjectRow (allRows declared 0 arms)
  | ok value =>
      simp only [usedCaseRows, observed]
      exact (Common.rowJoin_le_iff _ _ _).mpr ⟨le_join_left _ _,
        Common.rowLe_trans (usedRows_le_allRows floatCheck defaultEval environment guardEval declared value 0 arms)
          (le_join_right _ _)⟩

end Yulang.CommonCaseEffectPaths
