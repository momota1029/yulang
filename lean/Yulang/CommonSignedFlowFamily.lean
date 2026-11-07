import Yulang.CommonEffectRequestGeneration

/-!
# Recursive signed row families with empty upper bounds

A scheme is a finite graph of identity, signed transport and residual edges,
plus pure sinks. Its semantics closes arbitrary parameter seeds under finite
paths, after removing precisely seeds whose paths reach a pure sink. Cycles
are not truncated, and parameter rows need not have finite support.

This module handles graphs without required constant heads. Every such graph
has the empty model. Deciding consistency of heads with arbitrary signed paths,
value constraints and universal operation-local types remains separate.
-/
namespace Yulang.CommonSignedFlowFamily
open Common (Occurrence Row rowLe)
open CommonEffectRequestGeneration (Permission)

inductive Action where
  | identity
  | shift : Nat → Permission → Int → Action
  | residual : List Nat → Action
  deriving DecidableEq, Repr

def captured (handled : List Nat) (occurrence : Occurrence) : Bool :=
  handled.contains occurrence.1 && occurrence.2.all (fun weight => weight == 0)

theorem captured_exact (handled : List Nat) (occurrence : Occurrence) :
    captured handled occurrence = true ↔ CommonSignedRows.Capturable handled occurrence := by
  simp [captured, CommonSignedRows.Capturable]

def Action.run : Action → Occurrence → Option Occurrence
  | .identity, occurrence => some occurrence
  | .shift scope permission delta, occurrence =>
      some (CommonSignedRows.shiftOccurrence scope permission.allows delta occurrence)
  | .residual handled, occurrence => if captured handled occurrence then none else some occurrence

/-- Actual graph edges denote element transport, not arbitrary functions. -/
structure Edge (n : Nat) where
  source : Fin n
  target : Fin n
  action : Action
  deriving DecidableEq, Repr

structure Graph (n : Nat) where
  edges : List (Edge n)
  pure : List (Fin n)
  deriving DecidableEq, Repr

/-- Independent edge inclusion and pure-sink constraints. -/
def Models (graph : Graph n) (rows : Fin n → Row) : Prop :=
  (∀ edge ∈ graph.edges, ∀ source target,
    rows edge.source source → edge.action.run source = some target → rows edge.target target) ∧
  (∀ sink ∈ graph.pure, ∀ occurrence, ¬ rows sink occurrence)

inductive Path (graph : Graph n) : Fin n → Occurrence → Fin n → Occurrence → Prop where
  | nil (slot : Fin n) (occurrence : Occurrence) : Path graph slot occurrence slot occurrence
  | cons {edge : Edge n} {first next last : Occurrence} {target : Fin n} :
      edge ∈ graph.edges → edge.action.run first = some next →
      Path graph edge.target next target last → Path graph edge.source first target last

theorem Path.append {graph : Graph n} {first middle last : Fin n} {a b c : Occurrence}
    (before : Path graph first a middle b) (after : Path graph middle b last c) :
    Path graph first a last c := by
  induction before with
  | nil => exact after
  | cons member runs _ ih => exact .cons member runs (ih after)

theorem Path.models {graph : Graph n} {rows : Fin n → Row} (model : Models graph rows)
    {first last : Fin n} {a b : Occurrence} (path : Path graph first a last b)
    (present : rows first a) : rows last b := by
  induction path with
  | nil => exact present
  | cons member runs _ ih => exact ih (model.1 _ member _ _ present runs)

/-- Safe seeds form the greatest subset from which no pure sink is reached.
This is part of recursive graph interpretation, never a parameter premise. -/
def Safe (graph : Graph n) (slot : Fin n) (occurrence : Occurrence) : Prop :=
  ∀ target moved, Path graph slot occurrence target moved → target ∉ graph.pure

structure Scheme (n : Nat) where
  graph : Graph n
  deriving DecidableEq, Repr

def Scheme.instantiate (scheme : Scheme n) (parameters : Fin n → Row) : Fin n → Row :=
  fun target occurrence => ∃ source seed,
    parameters source seed ∧ Safe scheme.graph source seed ∧ Path scheme.graph source seed target occurrence

/-- All signed/residual cycles and all pure sinks, with unrestricted rows. -/
theorem all_parameters_models (scheme : Scheme n) (parameters : Fin n → Row) :
    Models scheme.graph (scheme.instantiate parameters) := by
  constructor
  · intro edge member source target present runs
    obtain ⟨slot, seed, parameter, safe, path⟩ := present
    exact ⟨slot, seed, parameter, safe, path.append (.cons member runs (.nil _ _))⟩
  · intro sink pure occurrence present
    obtain ⟨slot, seed, _, safe, path⟩ := present
    exact safe sink occurrence path pure

theorem model_seed_safe {graph : Graph n} {rows : Fin n → Row} (model : Models graph rows)
    (slot : Fin n) (occurrence : Occurrence) (present : rows slot occurrence) :
    Safe graph slot occurrence := by
  intro target moved path pure
  exact model.2 target pure moved (path.models model present)

/-- Original rows are recovered literally, including every independent slot. -/
theorem model_retraction (graph : Graph n) (rows : Fin n → Row) (model : Models graph rows) :
    (Scheme.mk graph).instantiate rows = rows := by
  funext target
  apply Common.rowLe_antisymm
  · rintro occurrence ⟨source, seed, present, _, path⟩
    exact path.models model present
  · intro occurrence present
    exact ⟨target, occurrence, present, model_seed_safe model target occurrence present, .nil _ _⟩

/-- Head-free graphs are always consistent; no check is hidden in membership. -/
def solve (graph : Graph n) : List (Scheme n) := [⟨graph⟩]

theorem returned_all_parameters (graph : Graph n) (scheme : Scheme n)
    (returned : scheme ∈ solve graph) (parameters : Fin n → Row) :
    Models graph (scheme.instantiate parameters) := by
  have same : scheme = ⟨graph⟩ := by simpa [solve] using returned
  subst scheme
  exact all_parameters_models _ parameters

theorem solve_all_instances_exact (graph : Graph n) (rows : Fin n → Row) :
    Models graph rows ↔ ∃ scheme ∈ solve graph, ∃ parameters : Fin n → Row,
      scheme.instantiate parameters = rows := by
  constructor
  · intro model
    exact ⟨⟨graph⟩, by simp [solve], rows, model_retraction graph rows model⟩
  · rintro ⟨scheme, returned, parameters, same⟩
    rw [← same]
    exact returned_all_parameters graph scheme returned parameters

/-- A syntactic residual edge has exactly the existing Common residual meaning. -/
theorem residual_edge_exact (handled : List Nat) (source target : Row) :
    (∀ a b, source a → (Action.residual handled).run a = some b → target b) ↔
      rowLe (CommonSignedRows.commonResidual handled source) target := by
  constructor
  · intro edge occurrence present
    have clear : captured handled occurrence = false := by
      cases capturedEq : captured handled occurrence with
      | false => rfl
      | true => exact False.elim (present.2 ((captured_exact _ _).mp capturedEq))
    exact edge occurrence occurrence present.1 (by simp [Action.run, clear])
  · intro included a b present runs
    have notCaptured : ¬ CommonSignedRows.Capturable handled a := by
      intro capture
      simp [Action.run, (captured_exact _ _).mpr capture] at runs
    have same : a = b := by
      have clear : captured handled a = false := by
        cases capturedEq : captured handled a with
        | false => rfl
        | true => exact False.elim (notCaptured ((captured_exact _ _).mp capturedEq))
      simpa [Action.run, clear] using runs
    subst b
    exact included a ⟨present, notCaptured⟩

/-- Signed edge semantics agrees with the total Common transport on all rows. -/
theorem shift_edge_exact (scope : Nat) (permission : Permission) (delta : Int)
    (source target : Row) :
    (∀ a b, source a → (Action.shift scope permission delta).run a = some b → target b) ↔
      rowLe (CommonSignedRows.transport scope permission.allows delta source) target := by
  constructor
  · intro edge occurrence present
    obtain ⟨seed, member, rfl⟩ := (CommonSignedRows.transport_member_iff _ _ _ _ _).mp present
    exact edge seed _ member rfl
  · intro included a b present runs
    have same : CommonSignedRows.shiftOccurrence scope permission.allows delta a = b :=
      Option.some.inj runs
    subst b
    exact included _ ((CommonSignedRows.transport_member_iff _ _ _ _ _).mpr ⟨a, present, rfl⟩)
end Yulang.CommonSignedFlowFamily
