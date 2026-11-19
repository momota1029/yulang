import Yulang.GeneralRebaseDiagnosticSource268
import Yulang.GeneralRebaseInspectionProbe268

namespace Yulang.GeneralRebaseIntegratedDiagnostic268
open GeneralDeclarations (Registry Declaration)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalCandidates (Metadata)
open GeneralNominalCenters (Site SameInputs)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalRecursiveCandidates (arguments)
open GeneralNominalVersionedCandidates231 (inputs)
open GeneralRebaseSourceSurvivor267 (Boundary Encoded)
open GeneralRebaseInspectionChecks268 (BoundList Head)
open GeneralRebasePartialBool268 (Answer Reflect)
open GeneralRebaseDiagnosticSource268 (Probes Sound)

def mergedOr (state : State roles) (focus : Occurrence roles) (fallback : Answer) : Answer :=
 (GeneralRebaseMergedGate268.probe state focus).orElse fun _ => fallback

theorem mergedOr_sound (registry : Registry) (state : State roles) (focus : Occurrence roles)
 (fallback : Answer) (witness : Reflect ((Boundary roles).MergedOutputConflict registry state focus) fallback) :
 Reflect ((Boundary roles).MergedOutputConflict registry state focus) (mergedOr state focus fallback) := by
 unfold mergedOr
 cases h : GeneralRebaseMergedGate268.probe state focus with
 | none => exact witness
 | some verdict =>
   simpa only [h,Option.orElse] using GeneralRebaseMergedGate268.probe_sound registry state focus

def enhance (registry : Registry) (state : State roles) (focus : Occurrence roles)
 (metadata : Answer) (head : Declaration → BoundList state.core.erased.current.context → Answer)
 (compare : Site roles → Site roles → Answer) (fallback : Probes) : Probes :=
 { fallback with
   inspection := (GeneralRebaseInspectionProbe268.probe registry state focus metadata head compare).orElse
     fun _ => fallback.inspection
   mergedConflict := mergedOr state focus fallback.mergedConflict }

theorem enhance_sound (registry : Registry) (state : State roles) (focus : Occurrence roles)
 (metadata : Answer) (head : Declaration → BoundList state.core.erased.current.context → Answer)
 (compare : Site roles → Site roles → Answer) (fallback : Probes) (sound : Sound registry state focus fallback)
 (metaSound : Reflect (Metadata (Encoded registry) state.core.erased.current.context) metadata)
 (headSound : ∀ decl ∈ (Encoded registry).declarations, ∀ bounds,
   arguments state.core.erased.current.context (inputs focus) = some bounds →
   Reflect (Head (Encoded registry) state.core.erased.current.context focus decl bounds) (head decl bounds))
 (compareSound : ∀ first ∈ state.core.sites, ∀ last ∈ state.core.sites,
   Reflect (SameInputs (Models state) first last) (compare first last)) :
 Sound registry state focus (enhance registry state focus metadata head compare fallback) := by
 refine ⟨sound.rootK2,sound.candidateK2,?_,sound.outputConflict,mergedOr_sound _ _ _ _ sound.mergedConflict,sound.sharingConflict⟩
 change Reflect ((Boundary roles).InspectionPending registry state focus)
   ((GeneralRebaseInspectionProbe268.probe registry state focus metadata head compare).orElse fun _ => fallback.inspection)
 cases h : GeneralRebaseInspectionProbe268.probe registry state focus metadata head compare with
 | none => exact sound.inspection
 | some verdict =>
   simpa only [h,Option.orElse] using GeneralRebaseInspectionProbe268.probe_sound registry state focus metadata head compare
     metaSound headSound compareSound

end Yulang.GeneralRebaseIntegratedDiagnostic268
