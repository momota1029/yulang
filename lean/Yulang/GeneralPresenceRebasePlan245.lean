import Yulang.GeneralPresencePreorderExtension245
import Yulang.GeneralPresenceCommonLaws245
/-! Finite plans of actual table rewrites preserve public solution sets.
Safe is a representation certificate, not a new source-language acceptance
criterion. Neither Safe-plan production nor termination of plan generation is
asserted. Private assignments may change while public coordinates stay exact. -/
namespace Yulang.GeneralPresenceRebasePlan245
open Core.PresenceGeneration
open GeneralPresenceDefinitionRewrite244 GeneralPresenceOwnerRewrite244
open GeneralPresenceCrossRead244 GeneralPresenceOwnerTable244
open GeneralPresenceOwnerOwnership244 GeneralPresenceModelCongruence245
open GeneralPresencePreorderExtension245
variable {Name Owner : Type} [DecidableEq Name] [DecidableEq Owner]

structure Edit (Name Owner : Type) where
 owner : Owner
 fresh : List (Entry Name)

structure Safe (sharedNames : Name → Prop) (state : State Name Owner) (edit : Edit Name Owner) : Prop where
 present : edit.owner ∈ state.owners
 disjoint : ∀ other ∈ state.owners, other ≠ edit.owner →
   DisjointTargets (state.entries edit.owner) (state.entries other)
 oldExternal : External (state.entries edit.owner)
 oldCoherent : Coherent (state.entries edit.owner)
 freshExternal : External edit.fresh
 freshCoherent : Coherent edit.fresh
 within : TargetsWithin edit.fresh (state.entries edit.owner)
 privateTargets : ∀ name, sharedNames name → ∀ entry ∈ state.entries edit.owner, entry.1 ≠ name

def run (state : State Name Owner) : List (Edit Name Owner) → State Name Owner
 | [] => state
 | edit :: rest => run (rebase state edit.owner edit.fresh) rest

inductive SafePlan (sharedNames : Name → Prop) : State Name Owner → List (Edit Name Owner) → Prop
 | nil (state) : SafePlan sharedNames state []
 | cons (state) (edit) (rest) (head : Safe sharedNames state edit)
   (tail : SafePlan sharedNames (rebase state edit.owner edit.fresh) rest) :
   SafePlan sharedNames state (edit :: rest)

def Projected (model : Model) (sharedNames : Name → Prop) (boundary : Name → Comp model)
 (state : State Name Owner) : Prop :=
 ∃ assignment, Models state model assignment ∧ Agrees sharedNames model assignment boundary

theorem step_exact (model : Model) (laws : Laws model) (sharedNames : Name → Prop)
 (boundary : Name → Comp model) (state : State Name Owner) (edit : Edit Name Owner)
 (safe : Safe sharedNames state edit) :
 Projected model sharedNames boundary state ↔
 Projected model sharedNames boundary (rebase state edit.owner edit.fresh) :=
 public_models_iff state edit.owner edit.fresh safe.present safe.disjoint safe.oldExternal
   safe.oldCoherent safe.freshExternal safe.freshCoherent safe.within sharedNames safe.privateTargets model laws boundary

theorem plan_exact (model : Model) (laws : Laws model) (sharedNames : Name → Prop)
 (boundary : Name → Comp model) (state : State Name Owner) (plan : List (Edit Name Owner))
 (safe : SafePlan sharedNames state plan) :
 Projected model sharedNames boundary state ↔ Projected model sharedNames boundary (run state plan) := by
 induction safe with
 | nil state => rfl
 | cons state edit rest head tail ih => exact (step_exact model laws sharedNames boundary state edit head).trans ih

/-- This specialization uses proved laws of the actual nominal Common model,
not an antisymmetry assumption on its syntax carrier. -/
theorem common_plan_exact (sharedNames : Name → Prop)
 (boundary : Name → Comp CommonNominalFullCarrier.model) (state : State Name Owner)
 (plan : List (Edit Name Owner)) (safe : SafePlan sharedNames state plan) :
 Projected CommonNominalFullCarrier.model sharedNames boundary state ↔
 Projected CommonNominalFullCarrier.model sharedNames boundary (run state plan) :=
 plan_exact _ GeneralPresenceCommonLaws245.common_laws sharedNames boundary state plan safe
end Yulang.GeneralPresenceRebasePlan245
