import Yulang.GeneralStoppedScalarStorage335
import Yulang.GeneralStoppedInstallHistory335

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralStoppedProjectedTrace335
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedKernel234 (Step At Administrative step_models)
open GeneralNominalRefinements (Refines)
open GeneralNominalReobservationSteps (PointClosed PointDescriptor PointParameter pointClosed_no_revision)
open GeneralStoppedLower335 (lower collect slotRows headAt descriptorAt record)
open GeneralStoppedShape335 (point descriptorExpr point_front)
open GeneralStoppedLowerOrigin335 (exists_entry)
open GeneralStoppedScalarStorage335 (inhabited_refinement)
open GeneralDeclarativeGrowth327 (Extends trans)
open GeneralDeclarativeWitnessHead334 (Slice)
open B4Target (Steps)

abbrev current (raw : State roles) := raw.core.erased.current.context.state
abbrev normalized (raw : State roles) := lower (current raw)

theorem point_parameters {xs : List (GeneralNominalState.Parameter n)}
    (encoded : point xs = some ids) :
    ∀ p ∈ xs, PointParameter p := by
  induction xs generalizing ids with
  | nil => intro _ placed; cases placed
  | cons x xs ih =>
    obtain ⟨one,rest,rfl,read,rfl⟩ := point_front x xs ids encoded
    intro p held
    rcases List.mem_cons.mp held with rfl|later
    · rfl
    · exact ih read _ later

theorem lowered_point_closed {raw : GeneralNominalState.State} (encoded : lower raw = some t) :
    PointClosed raw := by
  intro k descriptor found
  unfold lower at encoded
  obtain ⟨_,yes,_⟩ := Option.map_eq_some_iff.mp encoded
  obtain ⟨rows,kept⟩ := exists_entry yes (List.mem_ofFn.mpr ⟨k,rfl⟩)
  have shape : (descriptorExpr raw.base descriptor).isSome = true := by
    change raw.nominals k = some descriptor at found
    change (do
      let h ← headAt raw k
      let d ← record (raw.base.source k) (descriptorExpr raw.base) (raw.nominals k)
      pure (h++d)) = some rows at kept
    rw [found] at kept
    cases head : headAt raw k with
    | none => simp [head] at kept
    | some ordinary =>
      cases candidate : descriptorExpr raw.base descriptor with
      | none => simp [head,record,candidate] at kept
      | some expr => rfl
  unfold descriptorExpr at shape
  cases proper : point descriptor.arguments with
  | none => simp [proper] at shape
  | some _ => exact point_parameters proper

/-- Reobservation cannot start from a successfully lowered point
fragment. Every other actual operation has a source refinement,
including physical allocation during the actual install. -/
theorem step_refinement {before after : State roles}
    (step : Step r root before after) (known : normalized before = some s) :
    Nonempty (Refines (current before) (current after)) := by
  obtain ⟨_,_,at_⟩ := step
  cases at_ with
  | administrative action =>
    cases action with
    | enqueue => exact ⟨GeneralNominalRefinements.refl _⟩
    | equate => exact ⟨GeneralNominalRefinements.extended _ [] _⟩
    | refresh _ cert _ _ _ _ => exact ⟨cert.refines⟩
    | reobserve rev _ improved => exact (pointClosed_no_revision (lowered_point_closed known) rev improved).elim
  | refresh _ _ cert _ _ _ _ => exact ⟨cert.refines⟩
  | merge => exact ⟨GeneralNominalRefinements.extended _ [] _⟩
  | install effect ready novel =>
    let raw := effect.plan.packet.context.state
    have context := effect.frame.context_eq.trans (congrArg (fun core => core.erased.current.context) ready.snapshot_eq)
    have rawEq : raw = current before := congrArg GeneralNominalCandidates.Context.state context
    let rs := GeneralNominalVersionedInstallation231.reserved effect.plan.packet
    let atoms := GeneralNominalVersionedInstallation231.atoms effect.plan.packet
    let names := GeneralNominalVersionedInstallation231.allocated effect.plan.packet
    let refinement := GeneralNominalRefinements.extended raw rs atoms
    have exact : Refines raw ({ GeneralNominalState.extend raw rs atoms with allocated := raw.allocated ++ names }) :=
      { refinement with allocated := fun _ held => List.mem_append_left _ held }
    exact ⟨rawEq ▸ exact⟩

/-- This finite-path certificate states when every actual intermediate
state is in the same supported scalar/point fragment; it does not
assert all traces or all successful runs have the certificate. -/
inductive Trace (r : GeneralDeclarations.Registry) (root : GeneralSourceDictionaries.Occurrence roles) :
    State roles → State roles → GeneralDeclarativeHead320.State → GeneralDeclarativeHead320.State → Prop where
  | refl : normalized raw = some q → Trace r root raw raw q q
  | tail : Trace r root before mid source stage → Step r root mid after →
      normalized after = some target → Trace r root before after source target

theorem endpoint {before after : State roles} (history : Trace r root before after s t) :
    normalized before = some s ∧ normalized after = some t ∧ Steps (Step r root) before after := by
  induction history with
  | refl seen => exact ⟨seen,seen,.refl⟩
  | tail _ hop seen earlier => exact ⟨earlier.1,seen,.tail earlier.2.2 hop⟩

theorem sources_preserved {before after : State roles} (history : Trace r root before after s t) :
    ∀ m, Models after m → Extends s t := by
  induction history with
  | refl _ => exact fun _ _ => GeneralDeclarativeClauseBatch327.reflexive _
  | tail prior hop new ih =>
    intro m finished
    have old := (endpoint prior).2.1
    obtain ⟨refinement⟩ := step_refinement hop old
    exact trans (ih m (step_models hop finished)) (inhabited_refinement refinement old new finished.1.1)

theorem source_slice {before after : State roles} (history : Trace r root before after s t)
    (fit : Models after m) (done : Nat → Prop) :
    ∃ (support : GeneralDeclarativeOrigins321.Supported t done), Nonempty (Slice support) := by
  have shown := sources_preserved history m fit
  exact ⟨_,⟨GeneralStoppedSourceRefinement335.sourceSlice shown done⟩⟩

end Yulang.GeneralStoppedProjectedTrace335
