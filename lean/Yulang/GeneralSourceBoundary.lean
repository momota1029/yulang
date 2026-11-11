import Yulang.B4Skeleton
import Yulang.CommonRoleSourceIntervalBatches

/-!
# Available components of the general source boundary

This is the partial inventory permitted by the general-boundary task, not a
`B4Target.SourceBoundary` instance. The declaration carrier, source inspection
bridge, general survivors and saturation driver are still missing. In particular,
an ordinary equation graph is not identified with a role inspection graph.

The definitions below use all existing ordinary term constructors and arbitrary
Common assignments. Captured intervals belong to one candidate: this operation
does not conjoin alternative implementations. No field depends on a resolver's
returned classification. See the companion design note dated 2026-11-11.
-/
namespace Yulang.GeneralSourceBoundary

open Core.PresenceGeneration (Comp)
open PresenceNormalForm (Atom All)
open CommonRoleRegularGraph (Graph)
open CommonRoleOutermostResolver (Frontier Protocol FrontierExact)

abbrev Model (α : Type) := α → Comp Common.model
abbrev OrdinaryState (α : Type) := List (Atom α)
abbrev Argument (α : Type) := CommonRoleIntervalGeneration.Argument α

/-- The Nat is the captured source-variable identity, not a role identifier. -/
abbrev Capture (α : Type) := CommonRoleSourceIntervalBatches.Demand α

/-- Satisfaction by this assignment, not mere existence of some assignment. -/
def Models (state : OrdinaryState α) (assignment : Model α) : Prop :=
  All Common.model assignment state

/-- All self and cross checks for each repeated captured variable. -/
def Compatible (captures : List (Capture α)) (assignment : Model α) : Prop :=
  ∀ first ∈ captures, ∀ last ∈ captures, first.1 = last.1 →
    Common.Subtype (CommonRoleIntervalGeneration.eval assignment first.2.1)
      (CommonRoleIntervalGeneration.eval assignment last.2.2)

def reconcile (state : OrdinaryState α) (captures : List (Capture α)) : OrdinaryState α :=
  state ++ CommonRoleSourceIntervalBatches.generate captures

/-- Graph-local observation only; source lower-bound reconciliation is missing. -/
def GraphUnresolved (graph : Graph n) (lower : Fin n) : Prop :=
  graph lower = .unresolved

/-- Includes finite unrollings of anonymous cycles; nominal bodies stay opaque. -/
abbrev GraphK2 (graph : Graph n) (lower : Fin n) : Prop :=
  CommonRoleGraphBisimulation.RegularAt graph lower

/-- Concrete component signatures, deliberately omitting all unconnected fields.
The two graph families have different types and no assumed correspondence. -/
structure DefinedFields (slots : Nat) where
  ordinaryModels : OrdinaryState (Fin slots) → Model (Fin slots) → Prop
  capturedCompatible : List (Capture (Fin slots)) → Model (Fin slots) → Prop
  intervalConstraints : List (Capture (Fin slots)) → OrdinaryState (Fin slots)
  compileOrdinary : OrdinaryState (Fin slots) → CommonPresenceConstraintGraph.Compiled slots
  equationModels : (graph : CommonPresenceConstraintGraph.Compiled slots) →
    (Fin slots → Common.Row) → (Fin graph.size → Common.Ty) → Prop
  unresolved : {nodes : Nat} → Graph nodes → Fin nodes → Prop
  structuralCycle : {nodes : Nat} → Graph nodes → Fin nodes → Prop

/-- An inventory with concrete values, not obligations supplied by a caller. -/
def definedFields (slots : Nat) : DefinedFields slots where
  ordinaryModels := Models
  capturedCompatible := Compatible
  intervalConstraints := CommonRoleSourceIntervalBatches.generate
  compileOrdinary := CommonPresenceConstraintGraph.compile
  equationModels := CommonPresenceConstraintGraph.Compiled.Models
  unresolved := GraphUnresolved
  structuralCycle := GraphK2

/-- Exact reconciliation for every old state and every shared assignment. -/
theorem reconcile_models (state : OrdinaryState α) (captures : List (Capture α))
    (assignment : Model α) :
    Models (reconcile state captures) assignment ↔
      Models state assignment ∧ Compatible captures assignment := by
  change All Common.model assignment
    (state ++ CommonRoleSourceIntervalBatches.cross captures captures) ↔ _
  rw [PresenceNormalForm.all_append, CommonRoleSourceIntervalBatches.cross_exact]
  rfl

/-- The same reconciliation compiles to the real shared equation graph, with
exact readback of both type and row assignments. It does not solve that graph. -/
theorem reconcile_graph_models (state : OrdinaryState (Fin slots))
    (captures : List (Capture (Fin slots))) (assignment : Model (Fin slots)) :
    (∃ values : Fin (CommonPresenceConstraintGraph.compile (reconcile state captures)).size → Common.Ty,
      (CommonPresenceConstraintGraph.compile (reconcile state captures)).Models
        (fun index => (assignment index).2) values ∧
      (CommonPresenceConstraintGraph.compile (reconcile state captures)).readback
        (fun index => (assignment index).2) values = assignment) ↔
      Models state assignment ∧ Compatible captures assignment := by
  exact (CommonPresenceConstraintGraph.compile_atoms_exact
    (reconcile state captures) assignment).symm.trans (reconcile_models state captures assignment)

theorem unresolved_excludes_graphK2 (graph : Graph n) (lower : Fin n)
    (pending : GraphUnresolved graph lower) : ¬ GraphK2 graph lower := by
  intro cycle
  have detected := (CommonRoleGraphBisimulation.regular_at_exact graph lower).mpr cycle
  change graph lower = .unresolved at pending
  simp [CommonRoleGraphBisimulation.regularAt, pending] at detected

/- The addendum's guard can be stated without filling any missing source field.
These are interface checks for every boundary, not a concrete classification. -/

universe u
variable {v : B4Target.Vocabulary.{u}}

/-- Addendum (1), only reason (iii). The existing target is left unchanged. -/
def ResolvedEmpty (boundary : B4Target.SourceBoundary v) (registry : v.Registry)
    (state : v.State) (demand : v.Demand) : Prop :=
  ¬ boundary.RootPending registry state demand ∧
    ∀ key children, ¬ boundary.Survivor registry state demand key children

theorem pending_excludes_resolvedEmpty (boundary : B4Target.SourceBoundary v)
    (registry : v.Registry) (state : v.State) (demand : v.Demand)
    (pending : boundary.RootPending registry state demand) :
    ¬ ResolvedEmpty boundary registry state demand := by
  intro empty
  exact empty.1 pending

/-- A local obstruction before any executor or final-state assumptions: an
unresolved demand with no survivors prevents an exact legacy frontier. -/
theorem legacy_frontier_obstruction (boundary : B4Target.SourceBoundary v)
    (registry : v.Registry) (state : v.State) (demand : v.Demand)
    (pending : boundary.RootPending registry state demand)
    (empty : ∀ key children, ¬ boundary.Survivor registry state demand key children)
    (protocol : Protocol v.Demand)
    (identity : protocol.Local = B4Skeleton.Local boundary registry state) :
    ¬ FrontierExact protocol := by
  intro exactFrontier
  have pendingLocal : protocol.Local demand .pending := by
    rw [identity]
    exact .pending pending
  have rejectedLocal : protocol.Local demand .rejected := by
    rw [identity]
    exact .rejected (Or.inr (Or.inr empty))
  have first := (exactFrontier demand .pending).mpr pendingLocal
  have last := (exactFrontier demand .rejected).mpr rejectedLocal
  have impossible : (Frontier.pending : Frontier v.Demand) = .rejected := first.symm.trans last
  cases impossible

end Yulang.GeneralSourceBoundary
