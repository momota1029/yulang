import Yulang.CommonSignedSeedFamily

/-! Safety preimages in a fixed key/coordinate-length fiber. This concerns
reachability of any occurrence at a pure sink, not reachability of one point. -/
namespace Yulang.CommonSignedSafetyPreimage
open Common (Occurrence)
open CommonSignedFlowFamily (Action Graph Path Safe captured captured_exact)

structure Fiber where
  key : Nat
  width : Nat
  deriving DecidableEq, Repr

def Fiber.Contains (fiber : Fiber) (occurrence : Occurrence) : Prop :=
  occurrence.1 = fiber.key ∧ occurrence.2.length = fiber.width

def Fiber.zero (fiber : Fiber) : Occurrence := (fiber.key, List.replicate fiber.width 0)

@[simp] theorem Fiber.contains_zero (fiber : Fiber) : fiber.Contains fiber.zero := by
  simp [Contains, zero]

theorem Fiber.capturable_iff (fiber : Fiber) (occurrence : Occurrence)
    (within : fiber.Contains occurrence) (handled : List Nat) :
    CommonSignedRows.Capturable handled occurrence ↔
      fiber.key ∈ handled ∧ occurrence = fiber.zero := by
  rcases within with ⟨keyEq, lengthEq⟩
  constructor
  · rintro ⟨member, weights⟩
    refine ⟨keyEq ▸ member, Prod.ext keyEq ?_⟩
    have replicated : occurrence.2 = List.replicate occurrence.2.length 0 := by
      apply List.ext_getElem
      · simp
      · intro index hi hj
        rw [List.getElem_replicate]
        exact weights _ (List.getElem_mem hi)
    simpa [zero, lengthEq] using replicated
  · rintro ⟨member, rfl⟩
    simp [CommonSignedRows.Capturable, zero, member]

theorem shift_preserves (fiber : Fiber) (occurrence : Occurrence) (within : fiber.Contains occurrence)
    (scope : Nat) (permission : CommonEffectRequestGeneration.Permission) (delta : Int) :
    fiber.Contains (CommonSignedRows.shiftOccurrence scope permission.allows delta occurrence) := by
  simpa only [Fiber.Contains, CommonSignedRows.shiftOccurrence_key,
    CommonSignedRows.shiftOccurrence_length] using within

theorem run_preserves (fiber : Fiber) (action : Action) (source target : Occurrence)
    (within : fiber.Contains source) (runs : action.run source = some target) : fiber.Contains target := by
  cases action with
  | identity =>
    have same : source = target := Option.some.inj runs
    exact same ▸ within
  | shift scope permission delta =>
    have same : CommonSignedRows.shiftOccurrence scope permission.allows delta source = target :=
      Option.some.inj runs
    rw [← same]
    exact shift_preserves fiber source within scope permission delta
  | residual keys =>
    by_cases capture : captured keys source = true
    · simp [Action.run, capture] at runs
    · have same : source = target := by simpa [Action.run, capture] using runs
      exact same ▸ within

/-- Finite inverse of the universal-success condition. A discarded occurrence
satisfies the outgoing obligation without requiring a target occurrence. -/
def preimage (fiber : Fiber) (action : Action) (allowed : List Occurrence) : List Occurrence :=
  match action with
  | .identity => allowed
  | .shift scope permission delta =>
      allowed.map (CommonSignedRows.shiftOccurrence scope permission.allows (-delta))
  | .residual handled => if fiber.key ∈ handled then fiber.zero :: allowed else allowed

theorem preimage_exact (fiber : Fiber) (action : Action) (allowed : List Occurrence)
    (source : Occurrence) (within : fiber.Contains source) :
    source ∈ preimage fiber action allowed ↔
      ∀ target, action.run source = some target → target ∈ allowed := by
  cases action with
  | identity => simp [preimage, Action.run]
  | shift scope permission delta =>
    simp only [preimage, List.mem_map, Action.run, Option.some.injEq, forall_eq']
    constructor
    · rintro ⟨target, member, same⟩
      rw [← same]
      have inverse : CommonSignedRows.shiftOccurrence scope permission.allows delta
          (CommonSignedRows.shiftOccurrence scope permission.allows (-delta) target) = target := by
        simpa using CommonSignedRows.shiftOccurrence_inverse scope permission.allows (-delta) target
      rw [inverse]
      exact member
    · intro member
      exact ⟨CommonSignedRows.shiftOccurrence scope permission.allows delta source, member,
        CommonSignedRows.shiftOccurrence_inverse scope permission.allows delta source⟩
  | residual handled =>
    by_cases key : fiber.key ∈ handled
    · simp only [preimage, key, ↓reduceIte, List.mem_cons]
      constructor
      · rintro (rfl | member) target runs
        · have capture := (captured_exact handled fiber.zero).mpr
            ((fiber.capturable_iff _ fiber.contains_zero handled).mpr ⟨key, rfl⟩)
          simp [Action.run, capture] at runs
        · by_cases capture : captured handled source = true
          · simp [Action.run, capture] at runs
          · have same : source = target := by simpa [Action.run, capture] using runs
            exact same ▸ member
      · intro all
        by_cases capture : captured handled source = true
        · exact Or.inl ((fiber.capturable_iff source within handled).mp
            ((captured_exact _ _).mp capture)).2
        · exact Or.inr (all source (by simp [Action.run, capture]))
    · have capture : captured handled source = false := by
        cases found : captured handled source with
        | false => rfl
        | true => exact False.elim (key ((fiber.capturable_iff source within handled).mp
            ((captured_exact _ _).mp found)).1)
      simp [preimage, key, Action.run, capture]

theorem safe_successor {graph : Graph n} (edge : CommonSignedFlowFamily.Edge n)
    (member : edge ∈ graph.edges) (source target : Occurrence)
    (safe : Safe graph edge.source source) (runs : edge.action.run source = some target) :
    Safe graph edge.target target := by
  intro sink moved path pure
  exact safe sink moved (.cons member runs path) pure
end Yulang.CommonSignedSafetyPreimage
