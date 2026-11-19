import Yulang.GeneralRebaseSourceInstall267

namespace Yulang.GeneralRebaseExecutableInstall267
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalCenters (Plan)
open GeneralNominalVersionedJournal232 (State Effect)
open GeneralRebaseSourceSurvivor267 (Boundary Encoded declChecked)
open GeneralRebaseHeadProbe267 (atFocus Honest)
open GeneralRebaseSourceClassification267 (verdict)
open GeneralRebasePickPlan267 (pick)
open GeneralRebaseSourceSelect267 (Guard)
open GeneralRebaseInstallChecks267 (choice edgesRecorded)

/-- One sound progress fragment: a decided unique head, history-compatible,
with an as-yet unrecorded child edge. None is not absence of source Steps. -/
def select (state : State roles) (probe : Plan roles → Option Bool) (entries : List (Plan roles)) :
 Option (Plan roles) := do
 match verdict probe entries with
 | .unique target =>
   let plan ← pick probe entries target
   if choice state.core.erased.current plan.packet && !(edgesRecorded state.core.erased.current plan)
   then some plan else none
 | _ => none

theorem selection_parts (state : State roles) (probe : Plan roles → Option Bool) (entries : List (Plan roles))
 (found : select state probe entries = some plan) :
 ∃ key kids, verdict probe entries = .unique (key,kids) ∧ pick probe entries (key,kids) = some plan ∧
 choice state.core.erased.current plan.packet = true ∧ edgesRecorded state.core.erased.current plan = false := by
 cases chosen : verdict probe entries with
 | none => simp [select,chosen] at found
 | ambiguous first last => simp [select,chosen] at found
 | deferred => simp [select,chosen] at found
 | unique target =>
   rcases target with ⟨key,kids⟩
   cases result : pick probe entries (key,kids) with
   | none => simp [select,chosen,result] at found
   | some selected =>
     simp [select,chosen,result] at found
     obtain ⟨⟨choiceOK,missing⟩,equal⟩ := found
     cases equal
     exact ⟨key,kids,rfl,result,choiceOK,missing⟩

theorem select_with_witness (state : State roles) (probe : Plan roles → Option Bool) (entries : List (Plan roles))
 (chosen : verdict probe entries = .unique (key,kids)) (found : pick probe entries (key,kids) = some plan)
 (choiceOK : choice state.core.erased.current plan.packet = true)
 (novel : edgesRecorded state.core.erased.current plan = false) :
 select state probe entries = some plan := by
 simp [select,chosen,found,choiceOK,novel]

/-- The computed candidate is the exact plan of an actual install, provided
the independent local diagnostic guards and a joint residual model are
certified for it. No supplied path, Plan list, or role-uniqueness premise. -/
theorem source_step (registry : Registry) (state : State roles) (root focus : Occurrence roles)
 (checked : (Boundary roles).Checked registry)
 (reachable : B4TargetV8.Reachable (Boundary roles) registry root state)
 (generated : GeneralNominalSaturationState.Generated state.core.erased.current root focus)
 (metadata : GeneralNominalRecursiveCandidates.Metadata (Encoded registry) state.core.erased.current.context)
 (probe : Plan roles → Option Bool)
 (honest : Honest probe (atFocus (Encoded registry) state root focus (declChecked checked)))
 (found : select state probe (atFocus (Encoded registry) state root focus (declChecked checked)) = some plan)
 (guards : Guard registry state focus plan.packet.declaration.id)
 (residual : ∀ effect : Effect roles, effect.registry = Encoded registry → effect.snapshot = state.core →
    effect.plan = plan → ∃ model, GeneralNominalVersionedMixedMaterialization237.Residual state effect model) :
 ∃ effect : Effect roles, effect.registry = Encoded registry ∧ effect.snapshot = state.core ∧ effect.plan = plan ∧
 (Boundary roles).Step registry root state (GeneralNominalVersionedInstall232.install state effect) ∧
 (∃ model, GeneralNominalVersionedJournal232.Models (GeneralNominalVersionedInstall232.install state effect) model) := by
 obtain ⟨key,kids,chosen,picked,choiceOK,missing⟩ := selection_parts _ _ _ found
 have obs := (GeneralRebasePickPlan267.pick_sound probe _ _ picked).2.2
 have keyEq : plan.packet.declaration.id = key := (Prod.mk.inj obs).1
 have selected := GeneralRebaseSourceSelect267.selected_from_verdict registry state root focus checked reachable
   generated metadata probe honest chosen (keyEq ▸ guards)
 obtain ⟨effect,reg,atState,same,f,declEq,_⟩ := GeneralRebaseSourceSelect267.effect_of_pick
   registry state root focus checked reachable metadata probe honest picked selected
 have safeSelection := (f.symm ▸ selected :
   GeneralNominalVersionedMixedSourceBoundary234.Local registry state effect.plan.packet.site.occurrence (.selected key kids))
 rw [←declEq] at safeSelection
 have split := GeneralRebaseSourceInstall267.source_step registry state root checked reachable effect reg atState
   (f.symm ▸ generated) safeSelection (same.symm ▸ choiceOK) (residual effect reg atState same)
   (same.symm ▸ GeneralRebaseInstallChecks267.missing_edge_proves_novel state plan missing)
 exact ⟨effect,reg,atState,same,split⟩

end Yulang.GeneralRebaseExecutableInstall267
