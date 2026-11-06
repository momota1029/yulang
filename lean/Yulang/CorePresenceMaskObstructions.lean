import Yulang.PresenceRegularCoalescing

/-!
# Outer masking does not descend to unmasked data equivalence

The current demand mask forgets a hidden required field even when its payload
has no inhabitants. Consequently `required l never` and `bottom` have the same
unmasked data meaning, but their masked meanings differ. Unmasked data-subtype
retraction alone therefore cannot justify masking two different root layers.

The common-output-context theorem in `PresenceRegularCoalescing` remains valid:
it masks one shared outer layer with equal child predicates. The obstruction
below concerns the stronger, different claim of recovery after masking the
coalesced root and the independent solution root themselves.
-/

namespace Yulang.Core.PresenceMaskObstructions

open PresenceLayers (Layer)
open PresenceDataTypes (Ty Le never records)
open SourceDataRuntime (Value)
open PresenceRegularObservations (observe)

universe u
variable {State : Type u}

/-- A demanded field with an empty payload has no data inhabitants. -/
theorem required_never_eq_bottom (label : Nat) (state : State) :
    (Layer.required label state).denote (fun _ => never) =
      (Layer.bottom : Layer State).denote (fun _ => never) := by
  funext value
  apply propext
  constructor
  · rintro ⟨_, _, _, impossible⟩
    exact impossible
  · exact False.elim

/-- Erasing that required demand keeps the record shape requirement. -/
theorem required_never_mask_eq_records (hidden : List Nat) (label : Nat)
    (present : label ∈ hidden) (state : State) :
    ((Layer.required label state).mask hidden).denote (fun _ => never) = records := by
  simp only [Layer.mask, present, ↓reduceIte, Layer.denote, Layer.meaning]

/-- A nonempty mask distinguishes two extensionally equal input predicates. -/
theorem mask_does_not_respect_data_equality (hidden : List Nat) (label : Nat)
    (present : label ∈ hidden) :
    ∃ left right : Layer Unit,
      left.denote (fun _ => never) = right.denote (fun _ => never) ∧
      ¬ Le ((left.mask hidden).denote (fun _ => never))
        ((right.mask hidden).denote (fun _ => never)) := by
  refine ⟨.required label (), .bottom, required_never_eq_bottom label (), ?_⟩
  rw [required_never_mask_eq_records hidden label present ()]
  intro below
  exact below (.record []) trivial

/-- No function on extensional data predicates implements every layer mask,
even for one fixed empty payload assignment and one nonempty hidden-label set.
This is a representation obstruction, not a request to change the old mask. -/
theorem no_extensional_mask (hidden : List Nat) (label : Nat) (present : label ∈ hidden) :
    ¬ ∃ erase : Ty → Ty, ∀ layer : Layer Unit,
      erase (layer.denote (fun _ => never)) = (layer.mask hidden).denote (fun _ => never) := by
  rintro ⟨erase, exactMask⟩
  obtain ⟨left, right, equal, different⟩ := mask_does_not_respect_data_equality hidden label present
  apply different
  have equalMasks : (left.mask hidden).denote (fun _ => never) =
      (right.mask hidden).denote (fun _ => never) := by
    rw [← exactMask left, ← exactMask right, equal]
  exact fun _ valid => equalMasks ▸ valid

namespace Counterexample

open PresenceRegularCoalescing

/-- Slot zero is free; slot one is rigid bottom. -/
def graph : Graph 2 := fun index => if index = 0 then none else some .bottom

/-- The only constraint is x ≤ bottom. -/
def cache : List (Edge 2) := [(0, 1)]

/-- The free slot's independent solution is required 0 never. Its unmasked
meaning is empty at every depth, so it satisfies the cached upper bound. -/
def original : PresenceRegularObservations.Graph (Fin 2) := fun index =>
  if index = 0 then .required 0 1 else .bottom

def generated := coalesceGraph graph cache original original

theorem closed : Closed graph cache cache := by
  constructor
  · exact fun _ member => member
  · intro middle variableNode source target first _
    have pairEq : (source, middle) = (0, 1) := by simpa only [cache, List.mem_singleton] using first
    have middleEq : middle = 1 := congrArg Prod.snd pairEq
    subst middle
    simp [graph] at variableNode
  · intro source target left right sourceRigid _ edge
    have pairEq : (source, target) = (0, 1) := by simpa only [cache, List.mem_singleton] using edge
    have sourceEq : source = 0 := congrArg Prod.fst pairEq
    subst source
    simp [graph] at sourceRigid

theorem original_bottom (depth : Nat) : observe original depth 1 = never := by
  cases depth <;> simp [observe, original, Layer.denote, Layer.meaning]

theorem model : Models graph cache original id := by
  constructor
  · intro index layer rigid depth item
    by_cases first : index = 0
    · simp [graph, first] at rigid
    · have layerEq : layer = .bottom := by
        simpa only [graph, first, ↓reduceIte, Option.some.injEq, eq_comm] using rigid
      subst layer
      simp only [id_eq, observe, original, first, ↓reduceIte, Layer.denote, Layer.meaning]
  · intro edge member
    have pairEq : edge = (0, 1) := by simpa only [cache, List.mem_singleton] using member
    subst edge
    intro depth item held
    change (original 0).denote (observe original depth) item at held
    simp only [original, ↓reduceIte, Layer.denote, Layer.meaning, List.not_mem_nil, ↓reduceIte,
      PresenceDataTypes.required, original_bottom] at held
    obtain ⟨_, _, _, impossible⟩ := held
    exact impossible

/-- Ordinary kernel reduction verifies the root mask of the coalesced slot.
The required parameter is intersected with its propagated bottom upper bound. -/
theorem generated_mask_check :
    ((generated (.inl 0)).mask [0]).check (fun _ _ => false) (.record []) = false := by
  decide

theorem generated_mask_empty :
    ¬ ((generated (.inl 0)).mask [0]).denote (observe generated 0) (.record []) := by
  intro valid
  have checked := (Layer.check_exact (fun _ _ => false) (observe generated 0)
    (fun _ _ => by simp [observe, never]) ((generated (.inl 0)).mask [0]) (.record [])).mpr valid
  rw [generated_mask_check] at checked
  cases checked

theorem original_mask_inhabited :
    ((original 0).mask [0]).denote (observe original 0) (.record []) := by
  simp [original, Layer.mask, Layer.denote, Layer.meaning, records]

/-- Closedness and an independent unmasked cached solution do not imply
retraction after masking the two different root layers themselves. -/
theorem masked_root_retraction_fails :
    ¬ (((generated (.inl 0)).mask [0]).denote (observe generated 0) (.record []) ↔
      ((original 0).mask [0]).denote (observe original 0) (.record [])) := by
  intro recovered
  exact generated_mask_empty (recovered.mpr original_mask_inhabited)

end Counterexample

end Yulang.Core.PresenceMaskObstructions
