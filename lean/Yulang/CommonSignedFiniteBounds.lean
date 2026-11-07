import Yulang.CommonSignedChoiceDecision

/-!
Computed support for signed disjunctive row clauses with finite upper rows.
The same terminating prepare/delete algorithms start from the intersection
of the actual finite upper lists instead of unrestricted candidate sets.
Support is a proof specification of the computed check, never its input.
-/
namespace Yulang.CommonSignedFiniteBounds
open Common (Occurrence Row)
open CommonSignedChoicePreparation (Clause Graph destinationCandidates mem_destinationCandidates
  discover discover_some advance prepare prepare_invariant prepare_finished)
open CommonSignedChoiceRefinement (good good_exact removable removable_some refine refine_invariant
  refine_finished prune_no_discovery)
open CommonSignedSafetyPreparation (State allowed set set_same set_other)
open CommonSignedSafetyRefinement (prune)
open CommonSignedSafetyPreimage (Fiber preimage_exact run_preserves)

structure Upper (n : Nat) where
  slot : Fin n
  allowed : List Occurrence

structure Problem (n : Nat) where
  clauses : Graph n
  uppers : List (Upper n)

def Models (problem : Problem n) (rows : Fin n → Row) : Prop :=
  CommonSignedChoicePreparation.Models problem.clauses rows ∧
    ∀ upper ∈ problem.uppers, ∀ occurrence, rows upper.slot occurrence → occurrence ∈ upper.allowed

def Supported (problem : Problem n) (slot : Fin n) (occurrence : Occurrence) : Prop :=
  ∃ rows, Models problem rows ∧ rows slot occurrence

theorem supported_models (problem : Problem n) : Models problem (Supported problem) := by
  constructor
  · intro clause member source target present runs
    obtain ⟨rows, model, seed⟩ := present
    obtain ⟨slot, listed, next⟩ := model.1 clause member source target seed runs
    exact ⟨slot, listed, rows, model, next⟩
  · intro upper member occurrence present
    obtain ⟨rows, model, seed⟩ := present
    exact model.2 upper member occurrence seed

def addUpper (upper : Upper n) (state : State n) : State n :=
  set state upper.slot (some (upper.allowed.filter (fun occurrence => allowed (state upper.slot) occurrence)))

def initial : List (Upper n) → State n
  | [] => fun _ => none
  | upper :: rest => addUpper upper (initial rest)

theorem addUpper_allowed (upper : Upper n) (state : State n) (slot : Fin n) (occurrence : Occurrence) :
    allowed (addUpper upper state slot) occurrence = true ↔
      allowed (state slot) occurrence = true ∧ (slot = upper.slot → occurrence ∈ upper.allowed) := by
  by_cases same : slot = upper.slot
  · subst slot
    simp [addUpper, set_same, allowed, List.mem_filter, and_comm]
  · simp only [addUpper, set_other state upper.slot slot _ same]
    simp [same]

theorem initial_allowed (uppers : List (Upper n)) (slot : Fin n) (occurrence : Occurrence) :
    allowed (initial uppers slot) occurrence = true ↔
      ∀ upper ∈ uppers, upper.slot = slot → occurrence ∈ upper.allowed := by
  induction uppers with
  | nil => simp [initial, allowed]
  | cons upper rest ih =>
    rw [initial, addUpper_allowed, ih]
    constructor
    · rintro ⟨tail, head⟩ bound member same
      rcases List.mem_cons.mp member with equal | member
      · subst bound
        exact head same.symm
      · exact tail bound member same
    · intro allBounds
      exact ⟨fun bound member => allBounds bound (List.mem_cons_of_mem _ member),
        fun same => allBounds upper (List.mem_cons_self) same.symm⟩

theorem initial_finite (uppers : List (Upper n)) (upper : Upper n) (member : upper ∈ uppers) :
    ∃ values, initial uppers upper.slot = some values := by
  induction uppers with
  | nil => simp at member
  | cons head rest ih =>
    by_cases same : upper.slot = head.slot
    · refine ⟨head.allowed.filter (fun occurrence => allowed (initial rest head.slot) occurrence), ?_⟩
      simp only [initial, addUpper, same, set_same]
    · have tail : upper ∈ rest := by
        rcases List.mem_cons.mp member with equal | found
        · subst upper
          exact False.elim (same rfl)
        · exact found
      obtain ⟨values, found⟩ := ih tail
      exact ⟨values, (set_other (initial rest) head.slot upper.slot _ same).trans found⟩

def Bounded (uppers : List (Upper n)) (state : State n) : Prop :=
  ∀ upper ∈ uppers, ∃ values, state upper.slot = some values ∧
    ∀ occurrence ∈ values, occurrence ∈ upper.allowed

theorem initial_bounded (uppers : List (Upper n)) : Bounded uppers (initial uppers) := by
  intro upper member
  obtain ⟨values, found⟩ := initial_finite uppers upper member
  refine ⟨values, found, ?_⟩
  intro occurrence listed
  apply (initial_allowed uppers upper.slot occurrence).mp ?_ upper member rfl
  simpa only [found, allowed, List.contains_iff_mem] using listed

def Covers (problem : Problem n) (fiber : Fiber) (state : State n) : Prop :=
  ∀ slot occurrence, fiber.Contains occurrence → Supported problem slot occurrence →
    allowed (state slot) occurrence = true

theorem initial_covers (problem : Problem n) (fiber : Fiber) :
    Covers problem fiber (initial problem.uppers) := by
  intro slot occurrence _ supported
  apply (initial_allowed _ _ _).mpr
  intro upper member same
  subst slot
  exact (supported_models problem).2 upper member occurrence supported

theorem advance_bounded (problem : Problem n) (fiber : Fiber) (state : State n) (clause : Clause n)
    (found : discover problem.clauses state = some clause) (bounded : Bounded problem.uppers state) :
    Bounded problem.uppers (advance fiber state clause) := by
  have sourceNone := (discover_some problem.clauses state clause found).2.1
  intro upper member
  obtain ⟨values, atSlot, included⟩ := bounded upper member
  have different : upper.slot ≠ clause.source := by
    intro same
    rw [same, sourceNone] at atSlot
    cases atSlot
  exact ⟨values, (set_other state clause.source upper.slot _ different).trans atSlot, included⟩

theorem advance_covers (problem : Problem n) (fiber : Fiber) (state : State n) (clause : Clause n)
    (found : discover problem.clauses state = some clause) (covers : Covers problem fiber state) :
    Covers problem fiber (advance fiber state clause) := by
  obtain ⟨member, _, finite⟩ := discover_some problem.clauses state clause found
  intro slot occurrence within supported
  by_cases same : slot = clause.source
  · subst slot
    simp only [advance, set_same, allowed, List.contains_iff_mem]
    apply (preimage_exact fiber clause.action _ occurrence within).mpr
    intro target runs
    obtain ⟨slot, listed, next⟩ := (supported_models problem).1 clause member occurrence target supported runs
    apply (mem_destinationCandidates state clause target).mpr
    refine ⟨slot, listed, ?_⟩
    have accepted := covers slot target (run_preserves fiber clause.action occurrence target within runs) next
    have isFinite := finite slot listed
    cases atSlot : state slot with
    | none => simp [atSlot] at isFinite
    | some values => simpa [atSlot, allowed] using accepted
  · simpa only [advance, set_other state clause.source slot _ same] using covers slot occurrence within supported

theorem supported_good (problem : Problem n) (fiber : Fiber) (state : State n) (covers : Covers problem fiber state)
    (slot : Fin n) (occurrence : Occurrence) (within : fiber.Contains occurrence)
    (supported : Supported problem slot occurrence) : good problem.clauses state slot occurrence = true := by
  apply (good_exact problem.clauses state slot occurrence).mpr
  intro clause member same target runs
  subst slot
  obtain ⟨destination, listed, next⟩ := (supported_models problem).1 clause member occurrence target supported runs
  exact ⟨destination, listed, covers destination target (run_preserves fiber clause.action occurrence target within runs) next⟩

theorem prune_covers (problem : Problem n) (fiber : Fiber) (state : State n) (item : Fin n × Occurrence)
    (found : removable problem.clauses state = some item) (covers : Covers problem fiber state) :
    Covers problem fiber (prune state item) := by
  intro slot occurrence within supported
  obtain ⟨⟨values, atSlot, _⟩, failed⟩ := removable_some problem.clauses state item found
  by_cases same : slot = item.1
  · subst slot
    have accepted := covers item.1 occurrence within supported
    have different : occurrence ≠ item.2 := by
      intro same
      subst occurrence
      have valid := supported_good problem fiber state covers item.1 item.2 within supported
      simp [failed] at valid
    simpa [prune, CommonSignedSafetyPreparation.set, atSlot, allowed, different] using accepted
  · simpa [prune, CommonSignedSafetyPreparation.set, same] using covers slot occurrence within supported

theorem prune_bounded (uppers : List (Upper n)) (state : State n) (item : Fin n × Occurrence)
    (bounded : Bounded uppers state) : Bounded uppers (prune state item) := by
  intro upper member
  obtain ⟨values, atSlot, included⟩ := bounded upper member
  by_cases same : upper.slot = item.1
  · have atItem : state item.1 = some values := same ▸ atSlot
    refine ⟨values.filter (fun occurrence => decide (occurrence ≠ item.2)), ?_, ?_⟩
    · simp [prune, CommonSignedSafetyPreparation.set, same, atItem]
    · intro occurrence listed
      exact included occurrence (List.mem_filter.mp listed).1
  · exact ⟨values, by simpa [prune, CommonSignedSafetyPreparation.set, same] using atSlot, included⟩

def settle (problem : Problem n) (fiber : Fiber) : State n :=
  refine problem.clauses (prepare problem.clauses fiber (initial problem.uppers))

theorem settle_covers (problem : Problem n) (fiber : Fiber) : Covers problem fiber (settle problem fiber) := by
  apply refine_invariant problem.clauses (Covers problem fiber)
  · exact prune_covers problem fiber
  · apply prepare_invariant problem.clauses fiber (Covers problem fiber)
    · exact advance_covers problem fiber
    · exact initial_covers problem fiber

theorem settle_bounded (problem : Problem n) (fiber : Fiber) : Bounded problem.uppers (settle problem fiber) := by
  apply refine_invariant problem.clauses (Bounded problem.uppers)
  · exact fun state item _ => prune_bounded problem.uppers state item
  · apply prepare_invariant problem.clauses fiber (Bounded problem.uppers)
    · exact advance_bounded problem fiber
    · exact initial_bounded problem.uppers

theorem settle_no_discovery (problem : Problem n) (fiber : Fiber) :
    discover problem.clauses (settle problem fiber) = none := by
  apply refine_invariant problem.clauses (fun state => discover problem.clauses state = none)
  · exact prune_no_discovery problem.clauses
  · exact prepare_finished problem.clauses fiber (initial problem.uppers)

theorem settle_models (problem : Problem n) (fiber : Fiber) :
    Models problem (CommonSignedChoiceDecision.stateRows fiber (settle problem fiber)) := by
  refine ⟨CommonSignedChoiceDecision.stable_models problem.clauses fiber _ (settle_no_discovery problem fiber)
    (refine_finished problem.clauses _), ?_⟩
  intro upper member occurrence present
  obtain ⟨values, atSlot, included⟩ := settle_bounded problem fiber upper member
  apply included occurrence
  simpa only [atSlot, allowed, List.contains_iff_mem] using present.2

theorem settle_exact (problem : Problem n) (fiber : Fiber) (slot : Fin n) (occurrence : Occurrence)
    (within : fiber.Contains occurrence) :
    allowed (settle problem fiber slot) occurrence = true ↔ Supported problem slot occurrence :=
  ⟨fun accepted => ⟨CommonSignedChoiceDecision.stateRows fiber (settle problem fiber),
      settle_models problem fiber, within, accepted⟩,
    settle_covers problem fiber slot occurrence within⟩

def check (problem : Problem n) (slot : Fin n) (occurrence : Occurrence) : Bool :=
  allowed (settle problem ⟨occurrence.1, occurrence.2.length⟩ slot) occurrence

theorem check_exact (problem : Problem n) (slot : Fin n) (occurrence : Occurrence) :
    check problem slot occurrence = true ↔ Supported problem slot occurrence :=
  settle_exact problem ⟨occurrence.1, occurrence.2.length⟩ slot occurrence ⟨rfl, rfl⟩

theorem checked_successor (problem : Problem n) (clause : Clause n) (member : clause ∈ problem.clauses)
    (source target : Occurrence) (safe : check problem clause.source source = true)
    (runs : clause.action.run source = some target) :
    ∃ slot ∈ clause.targets, check problem slot target = true := by
  obtain ⟨slot, listed, supported⟩ := (supported_models problem).1 clause member source target
    ((check_exact problem clause.source source).mp safe) runs
  exact ⟨slot, listed, (check_exact problem slot target).mpr supported⟩

theorem checked_upper (problem : Problem n) (upper : Upper n) (member : upper ∈ problem.uppers)
    (occurrence : Occurrence) (safe : check problem upper.slot occurrence = true) : occurrence ∈ upper.allowed :=
  (supported_models problem).2 upper member occurrence ((check_exact problem upper.slot occurrence).mp safe)

end Yulang.CommonSignedFiniteBounds
