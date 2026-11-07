import Yulang.CommonClampedClosureSoundness

/-!
# Internal soundness for selected ordinary bound branches

The selection contains only finite syntax and structural proofs: original
node IDs, row checks, literal flags, child-edge closure, and strict source
descent for every branch that asks for current-depth children. It does not
contain a semantic solution or an assignment-dependent branch choice.

The finite inspection law is a separate internal lemma, supplied by the
actual bound inspector and constructor equations. Guarded and current-depth
child facts are then proved together by depth and source-measure induction.
Thus asking for both interpretations in a non-rigid branch does not leave
either one as an ordinary-subtype premise. This module does not assert that
a public inference algorithm has constructed such a finite selection.
-/

namespace Yulang.CommonClampedSelectedSoundness

open Common (Ty Row)
open PresenceOpenTailGenerationLowering (Pool)
open CommonPresenceConstraintGraph (EdgesHold rowEval)
open CommonClampedClosureSoundness (RigidEdges edge_at_of_rigid_source)
open CommonFiniteChildInspection (BelowAt GuardedAt CheckAt BranchAt)
open CommonSymbolicConstraints (Check Branch)

variable {m : Nat}

abbrev Edge (pool : Pool m) := Fin pool.size × Fin pool.size
abbrev Checks (pool : Pool m) :=
  Branch (Core.PresenceGeneration.RowTerm (Fin m)) (Fin pool.size) (Fin pool.size)

def OrdinaryCheck : Check Rows Node Child → Prop
  | .childBelow (.ref _) (.ref _) => True
  | .rowBelow _ _ | .flag (.literal _) => True
  | _ => False

/-- Structural data for a selected branch at every propagated rigid pair.
All fields are independent of rows, values and free parameters. -/
structure Selection (pool : Pool m) (edges : List (Edge pool)) where
  branch : Edge pool → Checks pool
  current : Edge pool → Bool
  measure : Fin pool.size → Nat
  ordinary : ∀ origin ∈ RigidEdges pool edges, ∀ check ∈ branch origin, OrdinaryCheck check
  childClosed : ∀ origin ∈ RigidEdges pool edges, ∀ first last,
    Check.childBelow (.ref first) (.ref last) ∈ branch origin → (first, last) ∈ edges
  currentDecreases : ∀ origin ∈ RigidEdges pool edges, current origin = true →
    ∀ first last, Check.childBelow (.ref first) (.ref last) ∈ branch origin →
      measure first < measure origin.1

def NonChildChecks (pool : Pool m) (edges : List (Edge pool)) (selection : Selection pool edges)
    (rows : Fin m → Row) (values : Fin pool.size → Ty) : Prop :=
  ∀ origin ∈ RigidEdges pool edges, ∀ check ∈ selection.branch origin,
    CommonClampedClosureSoundness.NonChildHolds pool rows values check

/-- The finite semantic interface supplied by an actual constructor inspector.
The two branch interpretations use the same selected finite list. -/
def FiniteInspection (pool : Pool m) (edges : List (Edge pool)) (selection : Selection pool edges)
    (rows : Fin m → Row) (values : Fin pool.size → Ty) : Prop :=
  ∀ depth origin, origin ∈ RigidEdges pool edges →
    BranchAt false depth (rowEval rows) values values (selection.branch origin) →
    (selection.current origin = true →
      BranchAt true depth (rowEval rows) values values (selection.branch origin)) →
    BelowAt depth (values origin.1) (values origin.2)

theorem guarded_branch (depth : Nat) (pool : Pool m) (edges : List (Edge pool))
    (selection : Selection pool edges) (rows : Fin m → Row) (values : Fin pool.size → Ty)
    (nonChild : NonChildChecks pool edges selection rows values)
    (guarded : ∀ edge ∈ edges, GuardedAt depth (values edge.1) (values edge.2))
    (origin : Edge pool) (member : origin ∈ RigidEdges pool edges) :
    BranchAt false depth (rowEval rows) values values (selection.branch origin) := by
  intro check included
  have plain := selection.ordinary origin member check included
  cases check with
  | childBelow firstPayload lastPayload =>
      cases firstPayload with
      | ref first =>
          cases lastPayload with
          | ref last => exact guarded (first, last) (selection.childClosed origin member first last included)
          | _ => cases plain
      | _ => cases plain
  | rowBelow | flag | profileBelow => exact nonChild origin member _ included

/-- Current-depth edges are derived from a strictly smaller source measure.
Variable upper/flow edges are already guaranteed by the clamped equations;
lower-to-variable edges keep their rigid source fixed during propagation. -/
theorem rigid_at_of_guarded (depth : Nat) (pool : Pool m) (edges : List (Edge pool))
    (selection : Selection pool edges) (rows : Fin m → Row)
    (parameters : Fin m → Ty) (values : Fin pool.size → Ty)
    (model : CommonPresenceTailRegular.Models (CommonPresenceClampedBounds.graph pool edges rows parameters) values)
    (inspected : FiniteInspection pool edges selection rows values)
    (nonChild : NonChildChecks pool edges selection rows values)
    (guarded : ∀ edge ∈ edges, GuardedAt depth (values edge.1) (values edge.2)) :
    ∀ origin ∈ RigidEdges pool edges, BelowAt depth (values origin.1) (values origin.2) := by
  have byMeasure : ∀ size, ∀ origin ∈ RigidEdges pool edges,
      selection.measure origin.1 = size → BelowAt depth (values origin.1) (values origin.2) := by
    intro size
    refine Nat.strongRecOn size ?_
    intro current ih origin member measured
    apply inspected depth origin member
    · exact guarded_branch depth pool edges selection rows values nonChild guarded origin member
    · intro requested check included
      have plain := selection.ordinary origin member check included
      cases check with
      | childBelow firstPayload lastPayload =>
          cases firstPayload with
          | ref first =>
              cases lastPayload with
              | ref last =>
                  have smaller := selection.currentDecreases origin member requested first last included
                  apply edge_at_of_rigid_source depth pool edges rows parameters values model
                    (first, last) (selection.childClosed origin member first last included)
                  intro target compared
                  exact ih (selection.measure first) (by omega) (first, target) compared rfl
              | _ => cases plain
          | _ => cases plain
      | rowBelow | flag | profileBelow => exact nonChild origin member _ included
  intro origin member
  exact byMeasure _ origin member rfl

/-- Both finite child interpretations have been discharged. The zero-depth
guarded case is trivial and each successor uses only the preceding depth. -/
theorem finite_edges (pool : Pool m) (edges : List (Edge pool))
    (selection : Selection pool edges) (rows : Fin m → Row)
    (parameters : Fin m → Ty) (values : Fin pool.size → Ty)
    (model : CommonPresenceTailRegular.Models (CommonPresenceClampedBounds.graph pool edges rows parameters) values)
    (inspected : FiniteInspection pool edges selection rows values)
    (nonChild : NonChildChecks pool edges selection rows values) (depth : Nat) :
    ∀ edge ∈ edges, BelowAt depth (values edge.1) (values edge.2) := by
  induction depth with
  | zero =>
      have rigid := rigid_at_of_guarded 0 pool edges selection rows parameters values model inspected nonChild
        (fun edge _ => CommonFiniteChildInspection.guarded_zero _ _)
      intro edge member
      exact edge_at_of_rigid_source 0 pool edges rows parameters values model edge member
        (fun target compared => rigid (edge.1, target) compared)
  | succ depth ih =>
      have rigid := rigid_at_of_guarded (depth + 1) pool edges selection rows parameters values model inspected nonChild
        (fun edge member => (CommonFiniteChildInspection.guarded_succ depth _ _).mpr (ih edge member))
      intro edge member
      exact edge_at_of_rigid_source (depth + 1) pool edges rows parameters values model edge member
        (fun target compared => rigid (edge.1, target) compared)

/-- Internal conditional soundness for finite selected ordinary branches.
No full ordinary edge or all-depth child comparison occurs among the premises.
The row/static checks and construction of a selection remain explicit tasks. -/
theorem conditional_soundness (pool : Pool m) (edges : List (Edge pool))
    (selection : Selection pool edges) (rows : Fin m → Row)
    (parameters : Fin m → Ty) (values : Fin pool.size → Ty)
    (model : CommonPresenceTailRegular.Models (CommonPresenceClampedBounds.graph pool edges rows parameters) values)
    (inspected : FiniteInspection pool edges selection rows values)
    (nonChild : NonChildChecks pool edges selection rows values) : EdgesHold edges values := by
  intro edge member depth
  exact finite_edges pool edges selection rows parameters values model inspected nonChild depth edge member

theorem solve_sound_of_selected (pool : Pool m) (edges : List (Edge pool))
    (selection : Selection pool edges) (rows : Fin m → Row)
    (parameters : Fin m → Ty) (recursiveParameters : Fin pool.size → Ty)
    (inspected : FiniteInspection pool edges selection rows
      (CommonPresenceClampedBounds.solve pool edges rows parameters recursiveParameters))
    (nonChild : NonChildChecks pool edges selection rows
      (CommonPresenceClampedBounds.solve pool edges rows parameters recursiveParameters)) :
    EdgesHold edges (CommonPresenceClampedBounds.solve pool edges rows parameters recursiveParameters) :=
  conditional_soundness pool edges selection rows parameters _
    (CommonPresenceTailRegular.solveBlock_models _ recursiveParameters) inspected nonChild

end Yulang.CommonClampedSelectedSoundness
