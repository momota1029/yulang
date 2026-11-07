import Yulang.PresenceLayers

/-! Finite alternatives for presence demands. Normalisation distributes only
the independently interpreted predicate connectives. It is not a rewrite of
legacy structural subtyping, which has a different lattice interpretation.
No satisfiability decision or regular principal coalescing is asserted. -/
namespace Yulang.Core.PresenceAlternatives

open PresenceLayers (Layer)
open SourceDataRuntime (Value)
universe u
variable {State : Type u}

abbrev Alternative (State : Type u) := List (Layer State)
abbrev Alternatives (State : Type u) := List (Alternative State)

def Conjunction (assignment : State → PresenceDataTypes.Ty) (hidden : List Nat)
    (atoms : Alternative State) (value : Value) : Prop :=
  ∀ atom ∈ atoms, atom.meaning assignment hidden value

def Holds (assignment : State → PresenceDataTypes.Ty) (hidden : List Nat)
    (choices : Alternatives State) (value : Value) : Prop :=
  ∃ atoms ∈ choices, Conjunction assignment hidden atoms value

def cross (left right : Alternatives State) : Alternatives State :=
  left.flatMap fun first => right.map (first ++ ·)

/-- No parameter is enumerated or restricted; alternatives retain complete
conjunctions, including constraints on other fields of the same record. -/
def normalise : Layer State → Alternatives State
  | .bottom => []
  | .top => [[]]
  | .union left right => normalise left ++ normalise right
  | .inter left right => cross (normalise left) (normalise right)
  | atom => [[atom]]

theorem conjunction_append (assignment : State → PresenceDataTypes.Ty) (hidden : List Nat)
    (left right : Alternative State) (value : Value) :
    Conjunction assignment hidden (left ++ right) value ↔
      Conjunction assignment hidden left value ∧ Conjunction assignment hidden right value := by
  simp [Conjunction, or_imp, forall_and]

theorem holds_append (assignment : State → PresenceDataTypes.Ty) (hidden : List Nat)
    (left right : Alternatives State) (value : Value) :
    Holds assignment hidden (left ++ right) value ↔
      Holds assignment hidden left value ∨ Holds assignment hidden right value := by
  simp [Holds, or_and_right, exists_or]

theorem holds_cross (assignment : State → PresenceDataTypes.Ty) (hidden : List Nat)
    (left right : Alternatives State) (value : Value) :
    Holds assignment hidden (cross left right) value ↔
      Holds assignment hidden left value ∧ Holds assignment hidden right value := by
  constructor
  · rintro ⟨atoms, member, valid⟩
    obtain ⟨first, firstMember, remaining⟩ := List.mem_flatMap.mp member
    obtain ⟨last, lastMember, rfl⟩ := List.mem_map.mp remaining
    have both := (conjunction_append assignment hidden first last value).mp valid
    exact ⟨⟨first, firstMember, both.1⟩, ⟨last, lastMember, both.2⟩⟩
  · rintro ⟨⟨first, firstMember, firstValid⟩, ⟨last, lastMember, lastValid⟩⟩
    exact ⟨first ++ last,
      List.mem_flatMap.mpr ⟨first, firstMember, List.mem_map.mpr ⟨last, lastMember, rfl⟩⟩,
      (conjunction_append assignment hidden first last value).mpr ⟨firstValid, lastValid⟩⟩

/-- Every layer, arbitrary child predicates, arbitrary masks and data values.
This is exact finite-alternative membership, without a solver hypothesis. -/
theorem normalise_exact (assignment : State → PresenceDataTypes.Ty) (hidden : List Nat)
    (layer : Layer State) (value : Value) :
    Holds assignment hidden (normalise layer) value ↔ layer.meaning assignment hidden value := by
  induction layer with
  | union left right ihl ihr =>
      exact (holds_append assignment hidden _ _ value).trans (or_congr ihl ihr)
  | inter left right ihl ihr =>
      exact (holds_cross assignment hidden _ _ value).trans (and_congr ihl ihr)
  | _ => simp [normalise, Holds, Conjunction, Layer.meaning,
      PresenceDataTypes.any, PresenceDataTypes.never]

def mask (hidden : List Nat) (choices : Alternatives State) : Alternatives State :=
  choices.map fun atoms => atoms.map (Layer.mask hidden)

/-- Mask every complete branch, preserving correlations and discarding
shadowed optional/lacks demands as well as required demands. -/
theorem mask_exact (assignment : State → PresenceDataTypes.Ty) (hidden outer : List Nat)
    (choices : Alternatives State) (value : Value) :
    Holds assignment outer (mask hidden choices) value ↔
      Holds assignment (hidden ++ outer) choices value := by
  constructor
  · rintro ⟨atoms, member, valid⟩
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    refine ⟨original, originalMember, ?_⟩
    intro atom atomMember
    exact (Layer.meaning_mask assignment hidden outer atom value).mp
      (valid _ (List.mem_map.mpr ⟨atom, atomMember, rfl⟩))
  · rintro ⟨atoms, member, valid⟩
    refine ⟨atoms.map (Layer.mask hidden), List.mem_map.mpr ⟨atoms, member, rfl⟩, ?_⟩
    intro atom atomMember
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp atomMember
    exact (Layer.meaning_mask assignment hidden outer original value).mpr (valid _ originalMember)

end Yulang.Core.PresenceAlternatives
