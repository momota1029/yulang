import Yulang.GeneralRebasePickPlan267
import Yulang.GeneralRebaseProspectiveCurrent264

namespace Yulang.GeneralRebaseSourceSelect267
open GeneralDeclarations (Registry)
open GeneralNominalCenters (Plan)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedJournal232 (State Effect)
open GeneralNominalSaturationState (Generated)
open GeneralNominalRecursiveCandidates (Metadata)
open GeneralNominalVersionedCandidates231 (Unique)
open GeneralRebaseSourceSurvivor267 (Boundary Encoded declChecked)
open GeneralRebaseHeadProbe267 (Honest atFocus atFocus_exact observation)
open GeneralRebaseSourceClassification267 (verdict source_valid)
open GeneralRebasePickPlan267 (pick picks_unique pick_sound)

structure Guard (registry : Registry) (state : State roles) (focus : Occurrence roles) (key : Nat) : Prop where
 safe : B4TargetV8.SafeKnown (Boundary roles) registry state focus
 clearOutput : ¬ (Boundary roles).OutputConflict registry state focus key
 clearMerged : ¬ (Boundary roles).MergedOutputConflict registry state focus
 clearSharing : ¬ (Boundary roles).SharingConflict registry state focus

theorem selected_of_unique (registry : Registry) (state : State roles) (focus : Occurrence roles)
 (guard : Guard registry state focus key)
 (unique : Unique (Encoded registry) state.core.erased.current.context focus key children) :
 GeneralNominalVersionedMixedSourceBoundary234.Local registry state focus (.selected key children) :=
 .ordinary guard.clearSharing (.ordinary guard.clearMerged (.selected guard.safe unique guard.clearOutput))

/-- Candidate discovery needs no caller-supplied candidate list. Diagnostics
and model truth are still separately certified. -/
theorem selected_from_verdict (registry : Registry) (state : State roles) (root focus : Occurrence roles)
 (checked : (Boundary roles).Checked registry)
 (reachable : B4TargetV8.Reachable (Boundary roles) registry root state)
 (generated : Generated state.core.erased.current root focus)
 (metadata : Metadata (Encoded registry) state.core.erased.current.context)
 (probe : Plan roles → Option Bool)
 (honest : Honest probe (atFocus (Encoded registry) state root focus (declChecked checked)))
 (chosen : verdict probe (atFocus (Encoded registry) state root focus (declChecked checked)) = .unique (key,children))
 (guard : Guard registry state focus key) :
 GeneralNominalVersionedMixedSourceBoundary234.Local registry state focus (.selected key children) := by
 have valid := source_valid registry state root focus checked reachable generated metadata probe honest
 rw [chosen] at valid
 exact selected_of_unique registry state focus guard valid

def effectFromPlan (registry : Registry) (state : State roles) (plan : Plan roles)
 (frame : GeneralNominalVersionedEvidence231.Frame registry state.core
   plan.packet.site.occurrence plan.packet.declaration.id plan)
 (unique : Unique registry state.core.erased.current.context plan.packet.site.occurrence
   plan.packet.declaration.id (GeneralNominalVersionedFrame231.children plan.packet))
 (ready : GeneralNominalCenteredHeadMatEffects.Ready state.core plan.packet.site.occurrence plan) : Effect roles :=
 ⟨registry,state.core,plan,frame,unique,ready⟩

/-- The returned effect uses the particular plan picked from the computed
table, rather than an unrelated existential Frame. -/
theorem effect_of_pick (registry : Registry) (state : State roles) (root focus : Occurrence roles)
 (checked : (Boundary roles).Checked registry)
 (reachable : B4TargetV8.Reachable (Boundary roles) registry root state)
 (metadata : Metadata (Encoded registry) state.core.erased.current.context)
 (probe : Plan roles → Option Bool)
 (honest : Honest probe (atFocus (Encoded registry) state root focus (declChecked checked)))
 (chosen : pick probe (atFocus (Encoded registry) state root focus (declChecked checked)) (key,children) = some plan)
 (selected : GeneralNominalVersionedMixedSourceBoundary234.Local registry state focus (.selected key children)) :
 ∃ effect : Effect roles,
 effect.registry = Encoded registry ∧ effect.snapshot = state.core ∧ effect.plan = plan ∧
 effect.plan.packet.site.occurrence = focus ∧ effect.plan.packet.declaration.id = key ∧
 GeneralNominalVersionedFrame231.children effect.plan.packet = children := by
 obtain ⟨member,positive,obs⟩ := pick_sound probe _ _ chosen
 obtain ⟨inReady,same⟩ := (atFocus_exact ..).mp member
 obtain ⟨shell,_,bits⟩ := (GeneralRebaseCandidatePrepared267.ready_exact ..).mp inReady
 have prepared := (GeneralRebaseCandidatePrepared267.prepared_iff _ _ _ _ shell).mpr
   ⟨metadata,bits,honest.positive plan member positive⟩
 have frame := GeneralRebaseEnumeratePlans267.frame_of_member (Encoded registry) state root (declChecked checked)
   plan ((GeneralRebaseEnumeratePlans267.plans_exact ..).mpr shell) prepared
 have selectedUnique := GeneralNominalVersionedMixedCurrentEvidence235.selected_unique
   (GeneralNominalVersionedMixedSourceBoundary234.local_iff.mp selected)
 obtain ⟨keyEq,childrenEq⟩ := Prod.mk.inj obs
 rw [←same,←keyEq,←childrenEq] at selectedUnique
 let effect := effectFromPlan (Encoded registry) state plan frame selectedUnique
   (GeneralNominalVersionedMixedReady235.ready checked reachable frame)
 exact ⟨effect,rfl,rfl,rfl,same,keyEq,childrenEq⟩

end Yulang.GeneralRebaseSourceSelect267
