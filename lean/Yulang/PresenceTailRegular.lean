import Yulang.PresenceTailElimination
import Yulang.PresenceMaskedCoalescing

/-!
# Closing unguarded presence tails into regular graphs

The finite positive tail eliminator is applied before guarded payload
references are tied into a regular graph. The resulting graph is defined for
every finite input and for every independently chosen external parameter
layer. It realizes all original equations at every depth and root mask.

Every independent masked regular solution is recovered by taking its root
layers as parameters. That choice occurs only in the completeness proof;
construction and soundness accept completely unrestricted parameters.

This does not add functions/effects to the data-observation model, decide
arbitrary producer inequalities or change `Core.infer`.
-/

namespace Yulang.PresenceTailElimination.Body

open PresenceLayers

variable {labels : Nat} {Payload Target Tail : Type}

def mapPayload (rename : Payload → Target) : Body labels Payload Tail → Body labels Target Tail
  | .atom layer => .atom (layer.map rename)
  | .ref tail => .ref tail
  | .union left right => .union (mapPayload rename left) (mapPayload rename right)
  | .inter left right => .inter (mapPayload rename left) (mapPayload rename right)
  | .mask hidden body => .mask hidden (mapPayload rename body)

theorem eval_mapPayload (body : Body labels Payload Tail) (rename : Payload → Target)
    (atoms : Layer Target → Mask labels → Prop)
    (tails : PositiveEquationElimination.Valuation (Tail × Mask labels)) (hidden : Mask labels) :
    (body.mapPayload rename).eval atoms tails hidden =
      body.eval (fun layer mask => atoms (layer.map rename) mask) tails hidden := by
  induction body generalizing hidden with
  | atom | ref => rfl
  | union left right ihLeft ihRight => simp only [mapPayload, eval, ihLeft, ihRight]
  | inter left right ihLeft ihRight => simp only [mapPayload, eval, ihLeft, ihRight]
  | mask more body ih => exact ih (hidden.join more)

theorem eval_congr (body : Body labels Payload Tail)
    (leftAtoms rightAtoms : Layer Payload → Mask labels → Prop)
    (leftTails rightTails : PositiveEquationElimination.Valuation (Tail × Mask labels))
    (atomsSame : ∀ layer hidden, leftAtoms layer hidden ↔ rightAtoms layer hidden)
    (tailsSame : ∀ coordinate, leftTails coordinate ↔ rightTails coordinate)
    (hidden : Mask labels) :
    body.eval leftAtoms leftTails hidden ↔ body.eval rightAtoms rightTails hidden := by
  induction body generalizing hidden with
  | atom layer => exact atomsSame layer hidden
  | ref tail => exact tailsSame (tail, hidden)
  | union left right ihLeft ihRight => exact or_congr (ihLeft hidden) (ihRight hidden)
  | inter left right ihLeft ihRight => exact and_congr (ihLeft hidden) (ihRight hidden)
  | mask more body ih => exact ih (hidden.join more)

end Yulang.PresenceTailElimination.Body

namespace Yulang.PresenceTailRegular

open PresenceLayers (Layer)
open PresenceTailElimination (Body Mask Coordinate)
open PresenceRegularObservations (observe)
open PresenceMaskedCoalescing (observeMasked)

variable {slots labels : Nat} {Index : Type}

abbrev Graph (slots labels : Nat) := PresenceTailElimination.Graph slots labels (Fin slots)

def liftGraph (graph : Graph slots labels) :
    PresenceTailElimination.Graph slots labels (Fin slots ⊕ Index) :=
  fun index => (graph index).mapPayload Sum.inl

def liftParameters (parameters : Fin slots → Layer Index) : Fin slots → Layer (Fin slots ⊕ Index) :=
  fun index => (parameters index).map Sum.inr

def solvedBody (graph : Graph slots labels) (parameters : Fin slots → Layer Index) :
    Fin slots → Layer (Fin slots ⊕ Index) :=
  PresenceTailElimination.solve (liftGraph graph) (liftParameters parameters)

/-- All same-depth edges have already been eliminated in `solvedBody`.
References in its ordinary layers are guarded payload edges. -/
def solveGraph (graph : Graph slots labels) (external : PresenceRegularObservations.Graph Index)
    (parameters : Fin slots → Layer Index) : PresenceRegularObservations.Graph (Fin slots ⊕ Index)
  | .inl index => solvedBody graph parameters index
  | .inr index => (external index).map Sum.inr

/-- Independent equations for a graph with possibly cyclic same-depth
references. Guards consume one depth; tail references retain that depth.
Both finite internal masks and every arbitrary outer mask are quantified. -/
def Realizes (graph : Graph slots labels) (original : PresenceRegularObservations.Graph Index)
    (roots : Fin slots → Index) : Prop :=
  ∀ depth outer hidden index value,
    (graph index).eval
      (fun layer mask => layer.meaning (fun child => observe original depth (roots child))
        (mask.names ++ outer) value)
      (fun coordinate => observeMasked original (depth + 1) (coordinate.2.names ++ outer)
        (roots coordinate.1) value) hidden ↔
    observeMasked original (depth + 1) (hidden.names ++ outer) (roots index) value

theorem parameter_embedding (graph : Graph slots labels)
    (external : PresenceRegularObservations.Graph Index) (parameters : Fin slots → Layer Index)
    (depth : Nat) (index : Index) (value : SourceDataRuntime.Value) :
    observe (solveGraph graph external parameters) depth (.inr index) value ↔
      observe external depth index value :=
  PresenceRegularObservations.observe_morphism external (solveGraph graph external parameters)
    Sum.inr (fun _ => rfl) depth index value

theorem parameter_mask_embedding (graph : Graph slots labels)
    (external : PresenceRegularObservations.Graph Index) (parameters : Fin slots → Layer Index)
    (depth : Nat) (hidden : List Nat) (index : Index) (value : SourceDataRuntime.Value) :
    observeMasked (solveGraph graph external parameters) depth hidden (.inr index) value ↔
      observeMasked external depth hidden index value := by
  cases depth with
  | zero => rfl
  | succ depth =>
      simp only [observeMasked, solveGraph, Layer.meaning_map]
      exact Layer.meaning_congr _ _ (parameter_embedding graph external parameters depth)
        hidden (external index) value

theorem observe_seed (family : Fin slots → Layer Payload)
    (assignment : Payload → PresenceDataTypes.Ty) (outer : List Nat)
    (value : SourceDataRuntime.Value) (coordinate : Coordinate slots labels) :
    PresenceTailElimination.observeFamily assignment outer value
        (PresenceTailElimination.seed family) coordinate =
      (family coordinate.1).meaning assignment (coordinate.2.names ++ outer) value :=
  propext (Layer.meaning_mask assignment coordinate.2.names outer (family coordinate.1) value)

theorem semanticStep_lift (graph : Graph slots labels)
    (family : Fin slots → Layer (Fin slots ⊕ Index))
    (assignment : (Fin slots ⊕ Index) → PresenceDataTypes.Ty) (outer : List Nat)
    (value : SourceDataRuntime.Value) (coordinate : Coordinate slots labels) :
    PresenceTailElimination.semanticStep (liftGraph graph) assignment outer value
        (PresenceTailElimination.observeFamily assignment outer value
          (PresenceTailElimination.seed family)) coordinate =
      (graph coordinate.1).eval
        (fun layer hidden => layer.meaning (fun child => assignment (.inl child))
          (hidden.names ++ outer) value)
        (fun child => (family child.1).meaning assignment (child.2.names ++ outer) value)
        coordinate.2 := by
  unfold PresenceTailElimination.semanticStep liftGraph
  rw [Body.eval_mapPayload]
  apply propext
  apply Body.eval_congr
  · intro layer hidden
    rw [Layer.meaning_mask, Layer.meaning_map]
  · intro child
    exact Iff.of_eq (observe_seed family assignment outer value child)

/-- Every finite input is realized at every observation depth and root mask,
for every independent external graph and every concrete parameter layer. -/
theorem solveGraph_realizes (graph : Graph slots labels)
    (external : PresenceRegularObservations.Graph Index) (parameters : Fin slots → Layer Index) :
    Realizes graph (solveGraph graph external parameters) Sum.inl := by
  intro depth outer hidden index value
  have fixed := congrFun
    (PresenceTailElimination.solve_satisfies (liftGraph graph) (liftParameters parameters)
      (observe (solveGraph graph external parameters) depth) outer value) (index, hidden)
  rw [semanticStep_lift, observe_seed] at fixed
  exact Iff.of_eq fixed

/-- Transfer independent realization across equality of all root-mask
observations; payload equality is obtained at the empty mask. -/
theorem realizes_congr {Other : Type} (graph : Graph slots labels)
    (left : PresenceRegularObservations.Graph Index) (leftRoots : Fin slots → Index)
    (right : PresenceRegularObservations.Graph Other) (rightRoots : Fin slots → Other)
    (same : ∀ depth hidden index value,
      observeMasked left depth hidden (leftRoots index) value ↔
        observeMasked right depth hidden (rightRoots index) value) :
    Realizes graph left leftRoots ↔ Realizes graph right rightRoots := by
  have bodySame (depth : Nat) (outer : List Nat) (hidden : Mask labels)
      (index : Fin slots) (value : SourceDataRuntime.Value) :
      (graph index).eval
          (fun layer mask => layer.meaning (fun child => observe left depth (leftRoots child))
            (mask.names ++ outer) value)
          (fun coordinate => observeMasked left (depth + 1) (coordinate.2.names ++ outer)
            (leftRoots coordinate.1) value) hidden ↔
        (graph index).eval
          (fun layer mask => layer.meaning (fun child => observe right depth (rightRoots child))
            (mask.names ++ outer) value)
          (fun coordinate => observeMasked right (depth + 1) (coordinate.2.names ++ outer)
            (rightRoots coordinate.1) value) hidden := by
    apply Body.eval_congr
    · intro layer mask
      apply Layer.meaning_congr
      intro child item
      simpa only [PresenceMaskedCoalescing.observeMasked_nil] using same depth [] child item
    · intro coordinate
      exact same (depth + 1) (coordinate.2.names ++ outer) coordinate.1 value
  constructor
  · intro valid depth outer hidden index value
    exact (bodySame depth outer hidden index value).symm.trans
      ((valid depth outer hidden index value).trans
        (same (depth + 1) (hidden.names ++ outer) index value))
  · intro valid depth outer hidden index value
    exact (bodySame depth outer hidden index value).trans
      ((valid depth outer hidden index value).trans
        (same (depth + 1) (hidden.names ++ outer) index value).symm)

/-- Any independently given masked regular solution is retracted. Arbitrary
same-depth tail cycles are allowed, without source provenance or guardedness.
Only guarded payload edges consume the induction depth. -/
theorem solveGraph_retract (graph : Graph slots labels)
    (original : PresenceRegularObservations.Graph Index) (roots : Fin slots → Index)
    (valid : Realizes graph original roots)
    (depth : Nat) (outer : List Nat) (index : Fin slots) (value : SourceDataRuntime.Value) :
    observeMasked (solveGraph graph original (fun index => original (roots index)))
        depth outer (.inl index) value ↔
      observeMasked original depth outer (roots index) value := by
  induction depth generalizing outer index value with
  | zero => rfl
  | succ depth ih =>
      let parameters : Fin slots → Layer Index := fun index => original (roots index)
      let result := solveGraph graph original parameters
      let assignment := observe result depth
      let lifted := liftParameters parameters
      have children (child : Fin slots) (item : SourceDataRuntime.Value) :
          assignment (.inl child) item ↔ observe original depth (roots child) item := by
        simpa only [PresenceMaskedCoalescing.observeMasked_nil] using ih [] child item
      have parametersExact (child : Fin slots) (hidden : List Nat) (item : SourceDataRuntime.Value) :
          (lifted child).meaning assignment hidden item ↔
            observeMasked original (depth + 1) hidden (roots child) item := by
        change ((original (roots child)).map Sum.inr).meaning (observe result depth) hidden item ↔ _
        rw [Layer.meaning_map]
        exact Layer.meaning_congr _ _
          (parameter_embedding graph original parameters depth) hidden (original (roots child)) item
      have fixed : PresenceTailElimination.semanticStep (liftGraph graph) assignment outer value
          (PresenceTailElimination.observeFamily assignment outer value
            (PresenceTailElimination.seed lifted)) =
          PresenceTailElimination.observeFamily assignment outer value
            (PresenceTailElimination.seed lifted) := by
        funext coordinate
        rw [semanticStep_lift, observe_seed]
        apply propext
        refine (Body.eval_congr (graph coordinate.1) _
          (fun layer hidden => layer.meaning (fun child => observe original depth (roots child))
            (hidden.names ++ outer) value) _
          (fun child => observeMasked original (depth + 1) (child.2.names ++ outer)
            (roots child.1) value) ?_ ?_ coordinate.2).trans ?_
        · intro layer hidden
          exact Layer.meaning_congr _ _ children (hidden.names ++ outer) layer value
        · intro child
          exact parametersExact child.1 (child.2.names ++ outer) value
        · exact (valid depth outer coordinate.2 coordinate.1 value).trans
            (parametersExact coordinate.1 (coordinate.2.names ++ outer) value).symm
      have retracted := congrFun
        (PresenceTailElimination.solveFamily_retract (liftGraph graph) lifted
          assignment outer value fixed) (index, Mask.empty)
      have resultExact : observeMasked result (depth + 1) outer (.inl index) value ↔
          (lifted index).meaning assignment outer value := by
        change (PresenceTailElimination.solveFamily (liftGraph graph) lifted (index, Mask.empty)).meaning
          assignment outer value ↔ (lifted index).meaning assignment outer value
        simpa only [PresenceTailElimination.observeFamily, PresenceTailElimination.seed,
          Mask.names_empty, Layer.mask_nil] using Iff.of_eq retracted
      exact resultExact.trans (parametersExact index outer value)

/-- Exact regular solved instances. For every candidate graph and root map,
independent realization is equivalent to being observationally equal to one
instance of the constructed scheme, at all depths, root masks and values. -/
theorem solved_instances_exact (graph : Graph slots labels)
    (original : PresenceRegularObservations.Graph Index) (roots : Fin slots → Index) :
    Realizes graph original roots ↔
      ∃ parameters : Fin slots → Layer Index,
        ∀ depth hidden index value,
          observeMasked (solveGraph graph original parameters) depth hidden (.inl index) value ↔
            observeMasked original depth hidden (roots index) value := by
  constructor
  · intro valid
    exact ⟨fun index => original (roots index), solveGraph_retract graph original roots valid⟩
  · rintro ⟨parameters, same⟩
    exact (realizes_congr graph (solveGraph graph original parameters) Sum.inl original roots same).mp
      (solveGraph_realizes graph original parameters)

end Yulang.PresenceTailRegular
