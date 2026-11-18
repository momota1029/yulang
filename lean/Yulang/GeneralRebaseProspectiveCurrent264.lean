import Yulang.GeneralRebaseProspectiveEffect263
import Yulang.GeneralNominalVersionedMixedMaterialization237
import Yulang.GeneralNominalVersionedMixedChoice236

namespace Yulang.GeneralRebaseProspectiveCurrent264
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232

/-- Source formation and a genuine current Frame discharge the request checker.
A previously possible internal-error branch is absent on this explicit domain. -/
theorem source_check
 (checked : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Checked registry)
 (reachable : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state)
 (frame : GeneralNominalVersionedEvidence231.Frame (GeneralNominalCenteredHeadAllocEncoding.registry registry)
   state.core demand key plan) :
 GeneralRebaseClassCheck261.check plan (GeneralRebaseExecutableRequests262.requests state.core demand) = .ok () := by
 rw [GeneralRebaseExecutableRequests262.requests_eq]
 exact (GeneralRebaseClassCheck261.actual_ready ..).mpr
   (GeneralNominalVersionedMixedReady235.ready checked reachable frame)

/-- No checker, translated-schema or position/alternative safety premises.
These follow from the actual selected current Frame and source reachability. -/
theorem source_checked_effect
 (checked : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Checked registry)
 (reachable : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state)
 (selected : GeneralNominalVersionedMixedSourceBoundary234.Local registry state demand (.selected key children)) :
 ∃ effect : Effect roles,
 effect.registry = GeneralNominalCenteredHeadAllocEncoding.registry registry ∧
 effect.snapshot = state.core ∧ effect.plan.packet.site.occurrence = demand ∧
 effect.plan.packet.declaration.id = key ∧ GeneralNominalVersionedFrame231.children effect.plan.packet = children ∧
 GeneralRebaseClassCheck261.check effect.plan (GeneralRebaseExecutableRequests262.requests state.core demand) = .ok () ∧
 (GeneralNominalVersionedPlans231.emittedSchema effect.plan).unknown = false ∧
 GeneralNominalVersionedCycles232.Safe state effect.plan ∧
 GeneralNominalVersionedMixedKernel234.AlternativesSafe (GeneralNominalCenteredHeadAllocEncoding.registry registry) state effect.plan.input := by
 obtain ⟨plan,frame,kids⟩ := GeneralNominalVersionedMixedSelectedFrame235.source_frame reachable selected
 have check := source_check checked reachable frame
 obtain ⟨effect,reg,snapshot,same,occurrence,identity,ordered⟩ :=
   GeneralRebaseProspectiveEffect263.checked_effect registry state demand key children selected plan frame check
 refine ⟨effect,reg,snapshot,occurrence,identity,ordered,?_,?_,?_,?_⟩
 · simpa only [same] using check
 · rw [same]; exact GeneralNominalVersionedMixedReady235.materialized reachable frame
 · rw [same]; exact GeneralNominalVersionedMixedGuardReduction235.positions
     (GeneralNominalVersionedMixedSourceBoundary234.local_iff.mp selected) frame
 · apply GeneralNominalVersionedMixedGuardReduction235.alternatives
   have equal := effect.plan.input_exact.trans occurrence
   rw [equal]
   exact GeneralNominalVersionedMixedSourceBoundary234.local_iff.mp selected

/-- A genuine restricted source class: one declaration key per role removes
historical choice compatibility, rather than presuming that guard. The single
joint residual model still contains real head/output/child obligations. -/
theorem role_unique_current
 (checked : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Checked registry)
 (reachable : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state)
 (effect : Effect roles)
 (reg : effect.registry = GeneralNominalCenteredHeadAllocEncoding.registry registry)
 (snapshot : effect.snapshot = state.core)
 (selected : GeneralNominalVersionedMixedSourceBoundary234.Local registry state effect.plan.packet.site.occurrence
   (.selected effect.plan.packet.declaration.id children))
 (uniqueRole : ∀ a ∈ (GeneralNominalCenteredHeadAllocEncoding.registry registry).declarations,
   ∀ b ∈ (GeneralNominalCenteredHeadAllocEncoding.registry registry).declarations, a.role = b.role → a.id = b.id)
 (common : ∃ model, GeneralNominalVersionedMixedMaterialization237.Residual state effect model) :
 GeneralNominalVersionedMixedCurrentCandidate235.Current (GeneralNominalCenteredHeadAllocEncoding.registry registry)
   state effect.plan.packet.site.occurrence effect := by
 have frame := effect.frame
 rw [reg,snapshot] at frame
 have choice := GeneralNominalVersionedMixedChoice236.choice_of_role_unique checked reachable selected
   frame.visible frame.role_eq uniqueRole
 apply GeneralNominalVersionedMixedGuardReduction235.current reg snapshot rfl
   (GeneralNominalVersionedMixedSourceBoundary234.local_iff.mp selected)
   (GeneralNominalVersionedMixedReady235.materialized reachable frame) choice
 obtain ⟨model,valid⟩ := common
 exact ⟨model,(GeneralNominalVersionedMixedMaterialization237.installation_models_iff checked reachable reg snapshot).mpr valid⟩
end Yulang.GeneralRebaseProspectiveCurrent264
