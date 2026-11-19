import Yulang.GeneralRebaseNoveltyProbe267
import Yulang.GeneralRebaseCertifiedPlanEntry267

namespace Yulang.GeneralRebaseInstallCandidates267
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalCenters (Plan)
open GeneralNominalVersionedJournal232 (State Effect)
open GeneralNominalRecursiveCandidates (Metadata)
open GeneralRebaseSourceSurvivor267 (Boundary Encoded declChecked)
open GeneralRebaseHeadProbe267 (Honest Match atFocus observation)
open GeneralRebaseSourceClassification267 (verdict)
open GeneralRebasePickPlan267 (matching matches_exact)
open GeneralRebaseSourceSelect267 (Guard)
open GeneralRebaseNoveltyProbe267 (novel)
open GeneralRebaseInstallChecks267 (choice semanticCommitted)
open GeneralNominalVersionedMixedMaterialization237 (Residual)
open GeneralNominalVersionedInstall232 (install)

def eligible (state : State roles) (head : Plan roles → Option Bool)
 (newSemantics joint : Plan roles → Bool) (target : Match roles) (plan : Plan roles) : Bool :=
 matching head target plan &&
 (choice state.core.erased.current plan.packet && (novel state newSemantics plan && joint plan))

/-- Keep all compatible concrete representatives of the uniquely certified
key and ordered children. Do not choose the first raw representation and
ignore later ones whose joint-model probe succeeds. -/
def scan (state : State roles) (head : Plan roles → Option Bool)
 (newSemantics joint : Plan roles → Bool) (entries : List (Plan roles)) : List (Plan roles) :=
 match verdict head entries with
 | .unique target => entries.filter (eligible state head newSemantics joint target)
 | _ => []

theorem scan_exact (state : State roles) (head : Plan roles → Option Bool)
 (newSemantics joint : Plan roles → Bool) (entries : List (Plan roles)) (plan : Plan roles) :
 plan ∈ scan state head newSemantics joint entries ↔ ∃ target,
 verdict head entries = .unique target ∧ plan ∈ entries ∧ head plan = some true ∧ observation plan = target ∧
 choice state.core.erased.current plan.packet = true ∧ novel state newSemantics plan = true ∧ joint plan = true := by
 cases h : verdict head entries with
 | none | ambiguous | deferred => simp [scan,h]
 | unique target =>
   simp only [scan,h,List.mem_filter,eligible,Bool.and_eq_true,matches_exact,
     GeneralRebasePartialClassification267.Verdict.unique.injEq,exists_eq_left',and_assoc]

/-- Independent contracts for the two additional positive semantic replies.
Neither requires proof that a negative or unknown reply is complete. -/
structure Probes (registry : Registry) (state : State roles) (newSemantics joint : Plan roles → Bool)
 (entries : List (Plan roles)) : Prop where
 novelSound : ∀ plan ∈ entries, newSemantics plan = true → ¬ semanticCommitted state plan
 jointSound : ∀ plan ∈ entries, joint plan = true → ∀ effect : Effect roles,
  effect.registry = registry → effect.snapshot = state.core → effect.plan = plan →
  ∃ model, Residual state effect model

theorem source_step (registry : Registry) (state : State roles) (root focus : Occurrence roles)
 (checked : (Boundary roles).Checked registry)
 (reachable : B4TargetV8.Reachable (Boundary roles) registry root state)
 (generated : GeneralNominalSaturationState.Generated state.core.erased.current root focus)
 (metadata : Metadata (Encoded registry) state.core.erased.current.context)
 (head : Plan roles → Option Bool) (newSemantics joint : Plan roles → Bool)
 (honest : Honest head (atFocus (Encoded registry) state root focus (declChecked checked)))
 (sound : Probes (Encoded registry) state newSemantics joint (atFocus (Encoded registry) state root focus (declChecked checked)))
 (plan : Plan roles)
 (member : plan ∈ scan state head newSemantics joint (atFocus (Encoded registry) state root focus (declChecked checked)))
 (guards : Guard registry state focus plan.packet.declaration.id) :
 ∃ effect : Effect roles, effect.registry = Encoded registry ∧ effect.snapshot = state.core ∧ effect.plan = plan ∧
 (Boundary roles).Step registry root state (install state effect) ∧
 (∃ model, GeneralNominalVersionedJournal232.Models (install state effect) model) := by
 obtain ⟨⟨key,kids⟩,chosen,listed,yes,obs,choiceOK,novelOK,jointOK⟩ := (scan_exact ..).mp member
 have sameKey := (Prod.mk.inj obs).1
 have selected := GeneralRebaseSourceSelect267.selected_from_verdict registry state root focus checked reachable
   generated metadata head honest chosen (sameKey ▸ guards)
 obtain ⟨effect,reg,atState,same,f,declEq,_⟩ :=
   GeneralRebaseCertifiedPlanEntry267.effect_of_entry registry state root focus checked reachable metadata head honest
     plan listed yes obs selected
 have safeSelection := (f.symm ▸ selected :
   GeneralNominalVersionedMixedSourceBoundary234.Local registry state effect.plan.packet.site.occurrence (.selected key kids))
 rw [←declEq] at safeSelection
 have common := sound.jointSound plan listed jointOK effect reg atState same
 have novelty := GeneralRebaseNoveltyProbe267.sound state newSemantics plan (sound.novelSound plan listed) novelOK
 have transition := GeneralRebaseSourceInstall267.source_step registry state root checked reachable effect reg atState
   (f.symm ▸ generated) safeSelection (same.symm ▸ choiceOK) common (same.symm ▸ novelty)
 exact ⟨effect,reg,atState,same,transition⟩

end Yulang.GeneralRebaseInstallCandidates267
