import Yulang.GeneralRebaseSourceInstall267

namespace Yulang.GeneralRebaseCertifiedPlanEntry267
open GeneralDeclarations (Registry)
open GeneralNominalCenters (Plan)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedJournal232 (State Effect)
open GeneralNominalRecursiveCandidates (Metadata)
open GeneralRebaseSourceSurvivor267 (Boundary Encoded declChecked)
open GeneralRebaseHeadProbe267 (atFocus atFocus_exact observation Honest)
open GeneralRebaseSourceSelect267 (effectFromPlan)

theorem effect_of_entry (registry : Registry) (state : State roles) (root focus : Occurrence roles)
 (checked : (Boundary roles).Checked registry)
 (reachable : B4TargetV8.Reachable (Boundary roles) registry root state)
 (metadata : Metadata (Encoded registry) state.core.erased.current.context)
 (probe : Plan roles → Option Bool)
 (honest : Honest probe (atFocus (Encoded registry) state root focus (declChecked checked)))
 (plan : Plan roles)
 (member : plan ∈ atFocus (Encoded registry) state root focus (declChecked checked))
 (positive : probe plan = some true)
 (observed : observation plan = (key,children))
 (selected : GeneralNominalVersionedMixedSourceBoundary234.Local registry state focus (.selected key children)) :
 ∃ effect : Effect roles,
 effect.registry = Encoded registry ∧ effect.snapshot = state.core ∧ effect.plan = plan ∧
 effect.plan.packet.site.occurrence = focus ∧ effect.plan.packet.declaration.id = key ∧
 GeneralNominalVersionedFrame231.children effect.plan.packet = children := by
 obtain ⟨inReady,same⟩ := (atFocus_exact ..).mp member
 obtain ⟨shell,_,bits⟩ := (GeneralRebaseCandidatePrepared267.ready_exact ..).mp inReady
 have prepared := (GeneralRebaseCandidatePrepared267.prepared_iff _ _ _ _ shell).mpr
   ⟨metadata,bits,honest.positive plan member positive⟩
 have frame := GeneralRebaseEnumeratePlans267.frame_of_member (Encoded registry) state root (declChecked checked)
   plan ((GeneralRebaseEnumeratePlans267.plans_exact ..).mpr shell) prepared
 have selectedUnique := GeneralNominalVersionedMixedCurrentEvidence235.selected_unique
   (GeneralNominalVersionedMixedSourceBoundary234.local_iff.mp selected)
 obtain ⟨keyEq,childrenEq⟩ := Prod.mk.inj observed
 rw [←same,←keyEq,←childrenEq] at selectedUnique
 let effect := effectFromPlan (Encoded registry) state plan frame selectedUnique
   (GeneralNominalVersionedMixedReady235.ready checked reachable frame)
 exact ⟨effect,rfl,rfl,rfl,same,keyEq,childrenEq⟩

end Yulang.GeneralRebaseCertifiedPlanEntry267
