import Yulang.GeneralSourceState
import Yulang.CommonCanonicalShapes
import Yulang.CommonPatternConcreteRecordTypes

/-!
# Checked normalized observations of a shared source state

The finite derivations below unfold recorded source equations and apply Common
laws. Complete record signatures contain every visible field, in label order.
An open residual retains its term and hidden labels and has no inspection edge.
In particular a repeated tail is not replaced by an empty record.

This is a partial, separately checked snapshot, not a total materializer.
Arrows, unresolved aliases, and expressions without a certified normal head
remain deferred. No candidate or executor is involved.
-/
namespace Yulang.GeneralNormalizedObservation

open GeneralSourceState (State Assignment Models)
open Core.PresenceGeneration (TyTerm)
open PresenceNormalForm (Atom)
open CommonRoleRegularGraph (Graph Node)

/-- Finite source normalization evidence. Unfolding follows existing equations;
it cannot add an equation to the ordinary state. -/
inductive Rewrites (state : State) : TyTerm (Fin state.slots) → TyTerm (Fin state.slots) → Prop
  | refl (term) : Rewrites state term term
  | trans : Rewrites state first middle → Rewrites state middle last → Rewrites state first last
  | head : (state.heads slot).equation = some term → Rewrites state (.var slot) term
  | ordinary : Atom.tyLe (.var slot) term ∈ state.ordinary →
      Atom.tyLe term (.var slot) ∈ state.ordinary → Rewrites state (.var slot) term
  | pair : Rewrites state a c → Rewrites state b d → Rewrites state (.pair a b) (.pair c d)
  | record : Rewrites state a b → Rewrites state rest tail →
      Rewrites state (.record label a rest) (.record label b tail)
  | variant : Rewrites state a b → Rewrites state (.variant tag a) (.variant tag b)
  | union : Rewrites state a c → Rewrites state b d → Rewrites state (.union a b) (.union c d)
  | required : Rewrites state (.required label payload) (.record label payload .emptyRecord)
  | shadow : Rewrites state (.record label payload (.record label hidden rest))
      (.record label payload rest)
  | swap : first ≠ last →
      Rewrites state (.record first a (.record last b rest)) (.record last b (.record first a rest))
  | merge : Rewrites state (.union (.variant tag a) (.variant tag b)) (.variant tag (.union a b))
  | idempotent : Rewrites state (.union term term) term

theorem rewrites_sound (derivation : Rewrites state first last) (model : Assignment)
    (models : Models state model) :
    Common.Equivalent (first.eval Common.model (state.assignment model))
      (last.eval Common.model (state.assignment model)) := by
  induction derivation with
  | refl => exact Common.equivalent_refl _
  | trans _ _ left right => exact Common.equivalent_trans left right
  | head recorded => exact GeneralSourceState.recorded_head_sound state model models _ _ recorded
  | ordinary forward backward => exact ⟨models.1 _ forward, models.1 _ backward⟩
  | pair _ _ left right => exact (CommonCanonicalShapes.pair_equivalent_iff ..).mpr ⟨left, right⟩
  | record _ _ payload tail =>
      exact ⟨Common.common_record_mono _ payload.1 tail.1,
        Common.common_record_mono _ payload.2 tail.2⟩
  | variant _ payload => exact (CommonCanonicalShapes.variant_equivalent_iff ..).mpr payload
  | union _ _ left right => exact CommonCanonicalShapes.union_congr left right
  | required => exact Common.equivalent_refl _
  | shadow => exact Common.common_shadowed_head_equivalent ..
  | swap different => exact CommonPatternConcreteRecordTypes.record_swap _ _ different _ _ _
  | merge => exact CommonCanonicalShapes.variant_union_group ..
  | idempotent =>
      exact ⟨(Common.common_union_is_join _ _ _).mpr ⟨Common.subtype_refl _, Common.subtype_refl _⟩,
        CommonBoundCoalescing.le_union_left _ _⟩

def recordTerm (fields : List (Nat × TyTerm α)) (tail : TyTerm α) : TyTerm α :=
  fields.foldr (fun field rest => .record field.1 field.2 rest) tail

/-- A complete record head uses the whole sorted visible label list. Required
fields and records with an empty tail share this representation. -/
inductive Shape where
  | pair
  | record (labels : List Nat)
  | variant (tag : Nat)
  | exactEmpty
  deriving DecidableEq

def Shape.Canonical : Shape → Prop
  | .record labels => labels.Pairwise (· < ·)
  | _ => True

def Shape.arity : Shape → Nat
  | .pair => 2
  | .record labels => labels.length
  | .variant _ => 1
  | .exactEmpty => 0

def Shape.term (shape : Shape) (children : Fin shape.arity → Fin slots) : TyTerm (Fin slots) :=
  match shape with
  | .pair => .pair (.var (children ⟨0, by simp [Shape.arity]⟩))
      (.var (children ⟨1, by simp [Shape.arity]⟩))
  | .record labels => recordTerm (List.ofFn (fun i : Fin labels.length =>
      (labels[i], TyTerm.var (children i)))) .emptyRecord
  | .variant tag => .variant tag (.var (children ⟨0, by simp [Shape.arity]⟩))
  | .exactEmpty => .exactEmpty

inductive Deferred (slots : Nat) where
  | unresolved
  /-- The prefix's labels are the residual's hidden labels. Its source references
  are retained even when unfolding the tail repeats the same context. -/
  | residual (fields : List (Nat × Fin slots)) (tail : TyTerm (Fin slots))
  | unsupported (term : TyTerm (Fin slots))

def Deferred.term : Deferred slots → Option (TyTerm (Fin slots))
  | .unresolved => none
  | .residual fields tail => some (recordTerm (fields.map fun field => (field.1, .var field.2)) tail)
  | .unsupported term => some term

inductive Head (shapes : Fin kinds → Shape) (slots : Nat) where
  | deferred (reason : Deferred slots)
  | scalar (base : Inference.Base)
  | structural (kind : Fin kinds) (children : Fin (shapes kind).arity → Fin slots)

def Head.term {shapes : Fin kinds → Shape} : Head shapes slots → Option (TyTerm (Fin slots))
  | .deferred reason => reason.term
  | .scalar base => some (.base base)
  | .structural kind children => some ((shapes kind).term children)

def Head.node {shapes : Fin kinds → Shape} : Head shapes slots → Node slots
  | .deferred _ => .unresolved
  | .scalar base => .scalar (CommonRoleScalarSourceInspection.code base)
  | .structural kind children => .structural kind.val (List.ofFn children)

/-- Every stored term has a finite normalization derivation from its original
source identity. Deferred observations make no readiness assertion. -/
structure Snapshot (state : State) where
  kinds : Nat
  shapes : Fin kinds → Shape
  shapes_injective : Function.Injective shapes
  canonical : ∀ kind, (shapes kind).Canonical
  heads : Fin state.slots → Head shapes state.slots
  checked : ∀ slot term, (heads slot).term = some term → Rewrites state (.var slot) term

def Snapshot.graph (view : Snapshot state) : Graph state.slots := fun slot => (view.heads slot).node

def ObservationModels (view : Snapshot state) (model : Assignment) : Prop :=
  ∀ slot term, (view.heads slot).term = some term →
    Common.Equivalent (model (state.source slot)).1
      (term.eval Common.model (state.assignment model))

theorem observation_models (view : Snapshot state) (model : Assignment)
    (models : Models state model) : ObservationModels view model := by
  intro slot term recorded
  exact rewrites_sound (view.checked slot term recorded) model models

theorem models_preserved (view : Snapshot state) (model : Assignment) :
    Models state model ∧ ObservationModels view model ↔ Models state model :=
  ⟨And.left, fun models => ⟨models, observation_models view model models⟩⟩

theorem deferred_graph (view : Snapshot state) (slot : Fin state.slots)
    (reason : Deferred state.slots) (deferred : view.heads slot = .deferred reason) :
    GeneralSourceBoundary.GraphUnresolved view.graph slot := by
  simp [GeneralSourceBoundary.GraphUnresolved, Snapshot.graph, deferred, Head.node]

/-- Removing a duplicate tag does not require a choice of payload assignment. -/
theorem duplicate_tag (state : State) (tag : Nat) (payload : TyTerm (Fin state.slots)) :
    Rewrites state (.union (.variant tag payload) (.variant tag payload)) (.variant tag payload) :=
  .trans .merge (.variant .idempotent)

theorem duplicate_tag_source (state : State) (slot : Fin state.slots) (tag : Nat)
    (payload : TyTerm (Fin state.slots))
    (forward : Atom.tyLe (.var slot) (.union (.variant tag payload) (.variant tag payload)) ∈ state.ordinary)
    (backward : Atom.tyLe (.union (.variant tag payload) (.variant tag payload)) (.var slot) ∈ state.ordinary) :
    Rewrites state (.var slot) (.variant tag payload) :=
  .trans (.ordinary forward backward) (duplicate_tag state tag payload)

theorem required_record_same (state : State) (label : Nat) (payload : Fin state.slots) :
    Rewrites state (.required label (.var payload)) ((Shape.record [label]).term (fun _ => payload)) ∧
      Rewrites state (.record label (.var payload) .emptyRecord)
        ((Shape.record [label]).term (fun _ => payload)) := by
  simp only [Shape.term, recordTerm, List.ofFn_succ, List.ofFn_zero, List.foldr_cons, List.foldr_nil]
  exact ⟨.required, .refl _⟩

end Yulang.GeneralNormalizedObservation
