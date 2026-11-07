import Yulang.PositiveEquationElimination
import Yulang.PresenceLayers

/-!
# Concrete masked solutions of unguarded presence-tail equations

`Body` separates guarded payload references, inside an existing presence
layer, from same-depth tail references. Tail references may occur under any
finite combination of union, intersection and field masks, and may form
arbitrary cycles without source provenance or guardedness.

Every finite input is expanded into `(tail, mask)` coordinates. The positive
fixed-point projection eliminates all same-depth references and returns
ordinary finite `PresenceLayers.Layer`s over the original guarded payloads.
Mask coherence is a syntactic invariant of the construction: masking a
result is exactly its result at the joined mask coordinate. Parameters are
ordinary layers chosen independently before solving, not predicates indexed
by an arbitrary observation depth or an assumed solution.

This is an exact solver for positive presence-demand equations. It is not
an all-input solver for producer inequalities, functions or effect rows.
-/

namespace Yulang.PresenceTailElimination

open PresenceLayers
open PositiveEquationElimination (Valuation Below Monotone iterate)

abbrev Mask (labels : Nat) := Fin labels → Bool

theorem sum_map_constant (items : List α) (constant : Nat) :
    (items.map fun _ => constant).sum = items.length * constant := by
  induction items with
  | nil => simp
  | cons item rest ih => simp [ih, Nat.succ_mul, Nat.add_comm]

namespace Mask

def empty : Mask labels := fun _ => false

def join (left right : Mask labels) : Mask labels := fun label => left label || right label

def only (label : Fin labels) : Mask labels := fun candidate => decide (candidate = label)

def names (hidden : Mask labels) : List Nat :=
  ((List.finRange labels).filter hidden).map Fin.val

def all : (labels : Nat) → List (Mask labels)
  | 0 => [fun index => Fin.elim0 index]
  | labels + 1 => (all labels).flatMap fun tail =>
      [Fin.cases false tail, Fin.cases true tail]

theorem all_complete (hidden : Mask labels) : hidden ∈ all labels := by
  induction labels with
  | zero =>
      have same : hidden = fun index => Fin.elim0 index := by
        funext index
        exact Fin.elim0 index
      simp [all, same]
  | succ labels ih =>
      have tail := ih (fun index => hidden index.succ)
      have eta : hidden = Fin.cases (hidden 0) (fun index => hidden index.succ) := by
        funext index
        exact Fin.cases rfl (fun _ => rfl) index
      unfold all
      apply List.mem_flatMap.mpr
      refine ⟨fun index => hidden index.succ, tail, ?_⟩
      rw [eta]
      cases hidden 0 <;> simp

theorem all_length (labels : Nat) : (all labels).length = 2 ^ labels := by
  induction labels with
  | zero => rfl
  | succ labels ih =>
      simp only [all, List.length_flatMap]
      change ((all labels).map fun _ => 2).sum = 2 ^ (labels + 1)
      rw [sum_map_constant, ih, Nat.pow_succ]

@[simp] theorem join_empty (hidden : Mask labels) : join hidden empty = hidden := by
  funext label
  simp [join, empty]

@[simp] theorem empty_join (hidden : Mask labels) : join empty hidden = hidden := by
  funext label
  simp [join, empty]

theorem join_comm (left right : Mask labels) : join left right = join right left := by
  funext label
  exact Bool.or_comm _ _

theorem join_assoc (first middle last : Mask labels) :
    join (join first middle) last = join first (join middle last) := by
  funext label
  exact Bool.or_assoc _ _ _

theorem join_right_comm (first middle last : Mask labels) :
    join (join first middle) last = join (join first last) middle := by
  rw [join_assoc, join_comm middle last, ← join_assoc]

@[simp] theorem names_empty : names (empty : Mask labels) = [] := by
  simp [names, empty]

theorem mem_names (hidden : Mask labels) (label : Nat) :
    label ∈ names hidden ↔ ∃ bound : label < labels, hidden ⟨label, bound⟩ = true := by
  constructor
  · intro member
    obtain ⟨index, present, same⟩ := List.mem_map.mp member
    subst label
    exact ⟨index.isLt, (List.mem_filter.mp present).2⟩
  · rintro ⟨bound, present⟩
    exact List.mem_map.mpr ⟨⟨label, bound⟩,
      List.mem_filter.mpr ⟨List.mem_finRange _, present⟩, rfl⟩

theorem mem_names_join (left right : Mask labels) (label : Nat) :
    label ∈ names (join left right) ↔ label ∈ names left ∨ label ∈ names right := by
  simp only [mem_names, join, Bool.or_eq_true]
  constructor
  · rintro ⟨bound, first | last⟩
    · exact Or.inl ⟨bound, first⟩
    · exact Or.inr ⟨bound, last⟩
  · rintro (⟨bound, first⟩ | ⟨bound, last⟩)
    · exact ⟨bound, Or.inl first⟩
    · exact ⟨bound, Or.inr last⟩

theorem mask_join (left right : Mask labels) (layer : Layer Payload) :
    (layer.mask (names left)).mask (names right) = layer.mask (names (join left right)) := by
  rw [Layer.mask_append]
  apply Layer.mask_congr
  intro label
  simp only [List.mem_append, mem_names_join]

theorem mask_only (label : Fin labels) (layer : Layer Payload) :
    layer.mask (names (only label)) = layer.mask [label.val] := by
  apply Layer.mask_congr
  intro candidate
  simp only [mem_names, only, decide_eq_true_eq, List.mem_singleton]
  constructor
  · rintro ⟨bound, same⟩
    exact congrArg Fin.val same
  · intro same
    subst candidate
    exact ⟨label.isLt, rfl⟩

end Mask

inductive Body (labels : Nat) (Payload Tail : Type) where
  | atom : Layer Payload → Body labels Payload Tail
  | ref : Tail → Body labels Payload Tail
  | union : Body labels Payload Tail → Body labels Payload Tail → Body labels Payload Tail
  | inter : Body labels Payload Tail → Body labels Payload Tail → Body labels Payload Tail
  | mask : Mask labels → Body labels Payload Tail → Body labels Payload Tail

namespace Body

variable {labels : Nat} {Payload Tail : Type}

def record (label : Fin labels) (payload : Payload) (tail : Body labels Payload Tail) :
    Body labels Payload Tail :=
  .inter (.atom (.required label.val payload)) (.mask (Mask.only label) tail)

/-- All tail lookups keep the observation depth. Only references already
inside an atom's presence layer are guarded payload references. -/
def expand (tails : Tail × Mask labels → Layer Payload) (hidden : Mask labels) :
    Body labels Payload Tail → Layer Payload
  | .atom layer => layer.mask hidden.names
  | .ref tail => tails (tail, hidden)
  | .union left right => .union (expand tails hidden left) (expand tails hidden right)
  | .inter left right => .inter (expand tails hidden left) (expand tails hidden right)
  | .mask more body => expand tails (hidden.join more) body

/-- Independent one-observation semantics, with arbitrary atom meanings. -/
def eval (atoms : Layer Payload → Mask labels → Prop)
    (tails : Valuation (Tail × Mask labels)) (hidden : Mask labels) :
    Body labels Payload Tail → Prop
  | .atom layer => atoms layer hidden
  | .ref tail => tails (tail, hidden)
  | .union left right => eval atoms tails hidden left ∨ eval atoms tails hidden right
  | .inter left right => eval atoms tails hidden left ∧ eval atoms tails hidden right
  | .mask more body => eval atoms tails (hidden.join more) body

theorem eval_monotone (body : Body labels Payload Tail)
    (atoms : Layer Payload → Mask labels → Prop)
    (left right : Valuation (Tail × Mask labels)) (below : Below left right)
    (hidden : Mask labels) : eval atoms left hidden body → eval atoms right hidden body := by
  induction body generalizing hidden with
  | atom => exact id
  | ref tail => exact below (tail, hidden)
  | union left right ihLeft ihRight => exact Or.imp (ihLeft hidden) (ihRight hidden)
  | inter left right ihLeft ihRight => exact And.imp (ihLeft hidden) (ihRight hidden)
  | mask more body ih => exact ih (hidden.join more)

/-- Mask coherence is preserved exactly at the syntax level, even for
non-injective mask shifts and arbitrary cyclic tail references. -/
theorem expand_mask (body : Body labels Payload Tail)
    (tails : Tail × Mask labels → Layer Payload)
    (coherent : ∀ tail first more,
      (tails (tail, first)).mask more.names = tails (tail, first.join more))
    (hidden more : Mask labels) :
    (body.expand tails hidden).mask more.names = body.expand tails (hidden.join more) := by
  induction body generalizing hidden with
  | atom layer => exact Mask.mask_join hidden more layer
  | ref tail => exact coherent tail hidden more
  | union left right ihLeft ihRight => simp only [expand, Layer.mask, ihLeft, ihRight]
  | inter left right ihLeft ihRight => simp only [expand, Layer.mask, ihLeft, ihRight]
  | mask further body ih =>
      simp only [expand, ih]
      rw [Mask.join_right_comm]

theorem meaning_expand (body : Body labels Payload Tail)
    (tails : Tail × Mask labels → Layer Payload)
    (assignment : Payload → PresenceDataTypes.Ty) (outer : List Nat)
    (hidden : Mask labels) (value : SourceDataRuntime.Value) :
    (body.expand tails hidden).meaning assignment outer value =
      body.eval (fun layer mask => (layer.mask mask.names).meaning assignment outer value)
        (fun coordinate => (tails coordinate).meaning assignment outer value) hidden := by
  induction body generalizing hidden with
  | atom | ref => rfl
  | union left right ihLeft ihRight =>
      simp only [expand, eval, Layer.meaning, PresenceDataTypes.union, ihLeft, ihRight]
  | inter left right ihLeft ihRight =>
      simp only [expand, eval, Layer.meaning, PresenceDataTypes.inter, ihLeft, ihRight]
  | mask more body ih => exact ih (hidden.join more)

end Body

abbrev Coordinate (slots labels : Nat) := Fin slots × Mask labels

abbrev Graph (slots labels : Nat) (Payload : Type) :=
  Fin slots → Body labels Payload (Fin slots)

def coordinates (slots labels : Nat) : List (Coordinate slots labels) :=
  (List.finRange slots).flatMap fun index => (Mask.all labels).map fun mask => (index, mask)

theorem coordinates_complete (coordinate : Coordinate slots labels) :
    coordinate ∈ coordinates slots labels := by
  exact List.mem_flatMap.mpr ⟨coordinate.1, List.mem_finRange _,
    List.mem_map.mpr ⟨coordinate.2, Mask.all_complete _, rfl⟩⟩

theorem coordinates_length (slots labels : Nat) :
    (coordinates slots labels).length = slots * 2 ^ labels := by
  simp only [coordinates, List.length_flatMap, List.length_map, Mask.all_length]
  rw [sum_map_constant, List.length_finRange]

def seed (parameters : Fin slots → Layer Payload) : Coordinate slots labels → Layer Payload :=
  fun coordinate => (parameters coordinate.1).mask coordinate.2.names

def step (graph : Graph slots labels Payload)
    (value : Coordinate slots labels → Layer Payload) : Coordinate slots labels → Layer Payload :=
  fun coordinate => (graph coordinate.1).expand value coordinate.2

def ascend (graph : Graph slots labels Payload)
    (value : Coordinate slots labels → Layer Payload) : Coordinate slots labels → Layer Payload :=
  fun coordinate => .union (value coordinate) (step graph value coordinate)

def descend (graph : Graph slots labels Payload)
    (value : Coordinate slots labels → Layer Payload) : Coordinate slots labels → Layer Payload :=
  fun coordinate => .inter (value coordinate) (step graph value coordinate)

/-- The number of rounds is obtained from the finite input dimensions. -/
def solveFamily (graph : Graph slots labels Payload) (parameters : Fin slots → Layer Payload) :
    Coordinate slots labels → Layer Payload :=
  iterate (descend graph) (coordinates slots labels).length
    (iterate (ascend graph) (coordinates slots labels).length (seed parameters))

def solve (graph : Graph slots labels Payload) (parameters : Fin slots → Layer Payload) :
    Fin slots → Layer Payload :=
  fun index => solveFamily graph parameters (index, Mask.empty)

def Coherent (family : Coordinate slots labels → Layer Payload) : Prop :=
  ∀ index hidden more, (family (index, hidden)).mask more.names = family (index, hidden.join more)

theorem seed_coherent (parameters : Fin slots → Layer Payload) :
    Coherent (seed (labels := labels) parameters) :=
  fun _ hidden more => Mask.mask_join hidden more _

theorem step_coherent (graph : Graph slots labels Payload)
    (family : Coordinate slots labels → Layer Payload) (coherent : Coherent family) :
    Coherent (step graph family) :=
  fun index hidden more => (graph index).expand_mask family coherent hidden more

theorem ascend_coherent (graph : Graph slots labels Payload)
    (family : Coordinate slots labels → Layer Payload) (coherent : Coherent family) :
    Coherent (ascend graph family) := by
  intro index hidden more
  simp only [ascend, Layer.mask]
  rw [coherent index hidden more, step_coherent graph family coherent index hidden more]

theorem descend_coherent (graph : Graph slots labels Payload)
    (family : Coordinate slots labels → Layer Payload) (coherent : Coherent family) :
    Coherent (descend graph family) := by
  intro index hidden more
  simp only [descend, Layer.mask]
  rw [coherent index hidden more, step_coherent graph family coherent index hidden more]

theorem iterate_invariant {Value : Type} (update : Value → Value) (invariant : Value → Prop)
    (preserved : ∀ value, invariant value → invariant (update value))
    (rounds : Nat) (initial : Value) (holds : invariant initial) :
    invariant (iterate update rounds initial) := by
  induction rounds generalizing initial with
  | zero => exact holds
  | succ rounds ih => exact ih (update initial) (preserved initial holds)

theorem solveFamily_coherent (graph : Graph slots labels Payload)
    (parameters : Fin slots → Layer Payload) : Coherent (solveFamily graph parameters) := by
  apply iterate_invariant (descend graph) Coherent (descend_coherent graph)
  apply iterate_invariant (ascend graph) Coherent (ascend_coherent graph)
  exact seed_coherent parameters

/-- The concrete mask family is determined by masking each single result
layer; no independently selected depth-indexed family is postulated. -/
theorem solve_mask (graph : Graph slots labels Payload) (parameters : Fin slots → Layer Payload)
    (index : Fin slots) (hidden : Mask labels) :
    (solve graph parameters index).mask hidden.names = solveFamily graph parameters (index, hidden) := by
  simpa only [solve, Mask.empty_join] using
    solveFamily_coherent graph parameters index Mask.empty hidden

def semanticStep (graph : Graph slots labels Payload)
    (assignment : Payload → PresenceDataTypes.Ty) (outer : List Nat)
    (value : SourceDataRuntime.Value) : Valuation (Coordinate slots labels) → Valuation (Coordinate slots labels) :=
  fun family coordinate => (graph coordinate.1).eval
    (fun layer hidden => (layer.mask hidden.names).meaning assignment outer value)
    family coordinate.2

def observeFamily (assignment : Payload → PresenceDataTypes.Ty) (outer : List Nat)
    (value : SourceDataRuntime.Value) (family : Coordinate slots labels → Layer Payload) :
    Valuation (Coordinate slots labels) :=
  fun coordinate => (family coordinate).meaning assignment outer value

theorem semanticStep_monotone (graph : Graph slots labels Payload)
    (assignment : Payload → PresenceDataTypes.Ty) (outer : List Nat)
    (value : SourceDataRuntime.Value) : Monotone (semanticStep graph assignment outer value) :=
  fun left right below coordinate => (graph coordinate.1).eval_monotone _ left right below coordinate.2

theorem observe_step (graph : Graph slots labels Payload)
    (assignment : Payload → PresenceDataTypes.Ty) (outer : List Nat)
    (value : SourceDataRuntime.Value) (family : Coordinate slots labels → Layer Payload) :
    observeFamily assignment outer value (step graph family) =
      semanticStep graph assignment outer value (observeFamily assignment outer value family) := by
  funext coordinate
  exact (graph coordinate.1).meaning_expand family assignment outer coordinate.2 value

theorem observe_ascend (graph : Graph slots labels Payload)
    (assignment : Payload → PresenceDataTypes.Ty) (outer : List Nat)
    (value : SourceDataRuntime.Value) (family : Coordinate slots labels → Layer Payload) :
    observeFamily assignment outer value (ascend graph family) =
      PositiveEquationElimination.ascend (semanticStep graph assignment outer value)
        (observeFamily assignment outer value family) := by
  funext coordinate
  change (_ ∨ _) = (_ ∨ _)
  rw [show (step graph family coordinate).meaning assignment outer value =
    semanticStep graph assignment outer value (observeFamily assignment outer value family) coordinate
      from congrFun (observe_step graph assignment outer value family) coordinate]
  rfl

theorem observe_descend (graph : Graph slots labels Payload)
    (assignment : Payload → PresenceDataTypes.Ty) (outer : List Nat)
    (value : SourceDataRuntime.Value) (family : Coordinate slots labels → Layer Payload) :
    observeFamily assignment outer value (descend graph family) =
      PositiveEquationElimination.descend (semanticStep graph assignment outer value)
        (observeFamily assignment outer value family) := by
  funext coordinate
  change (_ ∧ _) = (_ ∧ _)
  rw [show (step graph family coordinate).meaning assignment outer value =
    semanticStep graph assignment outer value (observeFamily assignment outer value family) coordinate
      from congrFun (observe_step graph assignment outer value family) coordinate]
  rfl

theorem observe_solveFamily (graph : Graph slots labels Payload)
    (parameters : Fin slots → Layer Payload) (assignment : Payload → PresenceDataTypes.Ty)
    (outer : List Nat) (value : SourceDataRuntime.Value) :
    observeFamily assignment outer value (solveFamily graph parameters) =
      PositiveEquationElimination.project (coordinates slots labels)
        (semanticStep graph assignment outer value)
        (observeFamily assignment outer value (seed parameters)) := by
  unfold solveFamily PositiveEquationElimination.project
  rw [PositiveEquationElimination.iterate_commute (descend graph)
    (PositiveEquationElimination.descend (semanticStep graph assignment outer value))
    (observeFamily assignment outer value) (observe_descend graph assignment outer value)]
  rw [PositiveEquationElimination.iterate_commute (ascend graph)
    (PositiveEquationElimination.ascend (semanticStep graph assignment outer value))
    (observeFamily assignment outer value) (observe_ascend graph assignment outer value)]

/-- Every finite input, including arbitrary same-depth cycles, is solved for
every independently chosen concrete parameter layer and payload assignment. -/
theorem solveFamily_sound (graph : Graph slots labels Payload)
    (parameters : Fin slots → Layer Payload) (assignment : Payload → PresenceDataTypes.Ty)
    (outer : List Nat) (value : SourceDataRuntime.Value) :
    semanticStep graph assignment outer value
        (observeFamily assignment outer value (solveFamily graph parameters)) =
      observeFamily assignment outer value (solveFamily graph parameters) := by
  rw [observe_solveFamily]
  exact PositiveEquationElimination.project_sound (coordinates slots labels) coordinates_complete
    (semanticStep graph assignment outer value) (semanticStep_monotone graph assignment outer value) _

/-- Any independent concrete masked solution is recovered, at every mask
coordinate. The premise is only used for completeness, never for construction
or for the preceding soundness theorem. -/
theorem solveFamily_retract (graph : Graph slots labels Payload)
    (solution : Fin slots → Layer Payload) (assignment : Payload → PresenceDataTypes.Ty)
    (outer : List Nat) (value : SourceDataRuntime.Value)
    (fixed : semanticStep graph assignment outer value
        (observeFamily assignment outer value (seed solution)) =
      observeFamily assignment outer value (seed solution)) :
    observeFamily assignment outer value (solveFamily graph solution) =
      observeFamily assignment outer value (seed solution) := by
  rw [observe_solveFamily]
  exact PositiveEquationElimination.project_retract _ _ _ fixed

theorem seed_solve (graph : Graph slots labels Payload)
    (parameters : Fin slots → Layer Payload) :
    seed (solve graph parameters) = solveFamily graph parameters := by
  funext coordinate
  exact solve_mask graph parameters coordinate.1 coordinate.2

/-- Independent equations, universally over guarded payload predicates,
outer masks and data values. No solver result occurs in this definition. -/
def Satisfies (graph : Graph slots labels Payload) (solution : Fin slots → Layer Payload) : Prop :=
  ∀ assignment outer value,
    semanticStep graph assignment outer value
        (observeFamily assignment outer value (seed solution)) =
      observeFamily assignment outer value (seed solution)

/-- Parameters are unrestricted concrete layers over the same guarded
payload references as the input. They need not be known solutions. -/
theorem solve_satisfies (graph : Graph slots labels Payload)
    (parameters : Fin slots → Layer Payload) : Satisfies graph (solve graph parameters) := by
  intro assignment outer value
  rw [seed_solve]
  exact solveFamily_sound graph parameters assignment outer value

def Equivalent (left right : Fin slots → Layer Payload) : Prop :=
  ∀ (assignment : Payload → PresenceDataTypes.Ty) outer index value,
    (left index).meaning assignment outer value ↔ (right index).meaning assignment outer value

theorem seed_equivalent (left right : Fin slots → Layer Payload)
    (same : Equivalent left right) (assignment : Payload → PresenceDataTypes.Ty)
    (outer : List Nat) (value : SourceDataRuntime.Value) :
    observeFamily assignment outer value (seed (labels := labels) left) =
      observeFamily assignment outer value (seed right) := by
  funext coordinate
  apply propext
  exact (Layer.meaning_mask assignment coordinate.2.names outer (left coordinate.1) value).trans
    ((same assignment (coordinate.2.names ++ outer) coordinate.1 value).trans
      (Layer.meaning_mask assignment coordinate.2.names outer (right coordinate.1) value).symm)

theorem satisfies_congr (graph : Graph slots labels Payload)
    (left right : Fin slots → Layer Payload) (same : Equivalent left right) :
    Satisfies graph left ↔ Satisfies graph right := by
  have familySame := seed_equivalent (labels := labels) left right same
  constructor
  · intro valid assignment outer value
    rw [← familySame assignment outer value]
    exact valid assignment outer value
  · intro valid assignment outer value
    rw [familySame assignment outer value]
    exact valid assignment outer value

theorem solve_retract (graph : Graph slots labels Payload)
    (solution : Fin slots → Layer Payload) (valid : Satisfies graph solution) :
    Equivalent (solve graph solution) solution := by
  intro assignment outer index value
  have retracted := congrFun
    (solveFamily_retract graph solution assignment outer value (valid assignment outer value))
    (index, Mask.empty)
  simpa only [solve, observeFamily, seed, Mask.names_empty, Layer.mask_nil] using
    Iff.of_eq retracted

/-- Exact complete instances for every finite positive tail graph. Cycles,
all union/intersection combinations and all representable masks are allowed. -/
theorem solved_instances_exact (graph : Graph slots labels Payload)
    (solution : Fin slots → Layer Payload) :
    Satisfies graph solution ↔
      ∃ parameters : Fin slots → Layer Payload, Equivalent (solve graph parameters) solution := by
  constructor
  · intro valid
    exact ⟨solution, solve_retract graph solution valid⟩
  · rintro ⟨parameters, same⟩
    exact (satisfies_congr graph (solve graph parameters) solution same).mp
      (solve_satisfies graph parameters)

end Yulang.PresenceTailElimination
