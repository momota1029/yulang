import Yulang.GeneralNominalVersionedMixedSelectedFrame235
import Yulang.GeneralRebaseClassCheck261
import Yulang.GeneralRebaseExecutableRequests262

namespace Yulang.GeneralRebaseProspectiveEffect263
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232

/-- Package a checked current source Frame, not a previously registered Plan.
This proof-level bridge does not search for candidates or prove Installable. -/
theorem checked_effect
 (registry : Registry) (state : State roles) (demand : Occurrence roles) (key : Nat)
 (children : List (Occurrence roles))
 (selected : GeneralNominalVersionedMixedSourceBoundary234.Local registry state demand (.selected key children))
 (plan : Plan roles)
 (frame : GeneralNominalVersionedEvidence231.Frame (GeneralNominalCenteredHeadAllocEncoding.registry registry)
   state.core demand key plan)
 (checked : GeneralRebaseClassCheck261.check plan
   (GeneralRebaseExecutableRequests262.requests state.core demand) = .ok ()) :
 ∃ effect : Effect roles,
 effect.registry = GeneralNominalCenteredHeadAllocEncoding.registry registry ∧
 effect.snapshot = state.core ∧ effect.plan = plan ∧
 effect.plan.packet.site.occurrence = demand ∧ effect.plan.packet.declaration.id = key ∧
 GeneralNominalVersionedFrame231.children effect.plan.packet = children := by
 have ready : GeneralNominalCenteredHeadMatEffects.Ready state.core demand plan := by
  rw [GeneralRebaseExecutableRequests262.requests_eq] at checked
  exact (GeneralRebaseClassCheck261.actual_ready ..).mp checked
 let effect := GeneralNominalVersionedMixedFrameSelection235.effect_of_selected
   (GeneralNominalVersionedMixedSourceBoundary234.local_iff.mp selected) frame ready
 exact ⟨effect,rfl,rfl,rfl,frame.occurrence_eq,frame.key_eq,
   (GeneralNominalVersionedMixedFrameSelection235.selected_identifies
     (GeneralNominalVersionedMixedSourceBoundary234.local_iff.mp selected) frame).2⟩

/-- Reachability supplies an actual current Frame. The check obligation is
explicitly attached to that chosen Plan; no all-candidate success is presumed. -/
theorem source_frame_then_check
 (registry : Registry) (root : Occurrence roles) (state : State roles)
 (reachable : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state)
 (demand : Occurrence roles) (key : Nat) (children : List (Occurrence roles))
 (selected : GeneralNominalVersionedMixedSourceBoundary234.Local registry state demand (.selected key children)) :
 ∃ plan : Plan roles,
 GeneralNominalVersionedEvidence231.Frame (GeneralNominalCenteredHeadAllocEncoding.registry registry)
   state.core demand key plan ∧
 GeneralNominalVersionedFrame231.children plan.packet = children ∧
 (GeneralRebaseClassCheck261.check plan (GeneralRebaseExecutableRequests262.requests state.core demand) = .ok () →
 ∃ effect : Effect roles,
 effect.registry = GeneralNominalCenteredHeadAllocEncoding.registry registry ∧
 effect.snapshot = state.core ∧ effect.plan = plan ∧
 effect.plan.packet.site.occurrence = demand ∧ effect.plan.packet.declaration.id = key ∧
 GeneralNominalVersionedFrame231.children effect.plan.packet = children) := by
 obtain ⟨plan,frame,childrenExact⟩ := GeneralNominalVersionedMixedSelectedFrame235.source_frame reachable selected
 exact ⟨plan,frame,childrenExact,checked_effect registry state demand key children selected plan frame⟩

/-- The actual chosen Frame either fails the internal request-layout check or
produces its precise Effect. A failure is not source-language rejection. -/
theorem source_outcome
 (registry : Registry) (root : Occurrence roles) (state : State roles)
 (reachable : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state)
 (demand : Occurrence roles) (key : Nat) (children : List (Occurrence roles))
 (selected : GeneralNominalVersionedMixedSourceBoundary234.Local registry state demand (.selected key children)) :
 ∃ plan : Plan roles,
 GeneralNominalVersionedEvidence231.Frame (GeneralNominalCenteredHeadAllocEncoding.registry registry)
   state.core demand key plan ∧
 GeneralNominalVersionedFrame231.children plan.packet = children ∧
 ((∃ reason, GeneralRebaseClassCheck261.check plan
   (GeneralRebaseExecutableRequests262.requests state.core demand) = .error reason) ∨
 (GeneralRebaseClassCheck261.check plan
   (GeneralRebaseExecutableRequests262.requests state.core demand) = .ok () ∧
 ∃ effect : Effect roles,
 effect.registry = GeneralNominalCenteredHeadAllocEncoding.registry registry ∧
 effect.snapshot = state.core ∧ effect.plan = plan ∧
 effect.plan.packet.site.occurrence = demand ∧ effect.plan.packet.declaration.id = key ∧
 GeneralNominalVersionedFrame231.children effect.plan.packet = children)) := by
 obtain ⟨plan,frame,childrenExact,complete⟩ := source_frame_then_check registry root state reachable demand key children selected
 refine ⟨plan,frame,childrenExact,?_⟩
 cases result : GeneralRebaseClassCheck261.check plan
   (GeneralRebaseExecutableRequests262.requests state.core demand) with
 | error reason => exact Or.inl ⟨reason,rfl⟩
 | ok value =>
   cases value
   exact Or.inr ⟨rfl,complete result⟩
end Yulang.GeneralRebaseProspectiveEffect263
