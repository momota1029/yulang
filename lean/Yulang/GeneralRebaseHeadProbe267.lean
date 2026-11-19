import Yulang.GeneralRebaseSourceSurvivor267

namespace Yulang.GeneralRebaseHeadProbe267
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalCenters (Plan)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedCandidates231 (Survivor)
open GeneralNominalSaturationState (Generated)
open GeneralNominalRecursiveCandidates (Metadata)
open GeneralRebaseSourceSurvivor267 (Boundary Encoded declChecked from_survivor to_survivor)
open GeneralRebaseCandidatePrepared267 (readyPlans headCondition)
open GeneralRebaseOccurrenceEq267 (same same_exact)

abbrev Match (roles : Roles.RoleDecls) := Nat × List (Occurrence roles)

def observation (plan : Plan roles) : Match roles :=
 (plan.packet.declaration.id,GeneralNominalVersionedFrame231.children plan.packet)

def atFocus (registry : Registry) (state : State roles) (root focus : Occurrence roles)
 (checked : GeneralRebaseCandidatePlan267.DeclChecked registry roles) : List (Plan roles) :=
 (readyPlans registry state root checked).filter fun plan => same plan.packet.site.occurrence focus

theorem atFocus_exact (registry : Registry) (state : State roles) (root focus : Occurrence roles)
 (checked : GeneralRebaseCandidatePlan267.DeclChecked registry roles) (plan : Plan roles) :
 plan ∈ atFocus registry state root focus checked ↔
 plan ∈ readyPlans registry state root checked ∧ plan.packet.site.occurrence = focus := by
 simp only [atFocus,List.mem_filter,same_exact]

/-- A probe may return unknown. Neither successful checking of some other
candidate nor a missing certificate makes unknown equivalent to false. -/
structure Honest (probe : Plan roles → Option Bool) (entries : List (Plan roles)) : Prop where
 positive : ∀ plan ∈ entries, probe plan = some true → headCondition plan
 negative : ∀ plan ∈ entries, probe plan = some false → ¬ headCondition plan

def positive (probe : Plan roles → Option Bool) (entries : List (Plan roles)) : List (Match roles) :=
 (entries.filter fun plan => probe plan == some true).map observation

def unresolved (probe : Plan roles → Option Bool) (entries : List (Plan roles)) : List (Plan roles) :=
 entries.filter fun plan => (probe plan).isNone

theorem positive_exact (probe : Plan roles → Option Bool) (entries : List (Plan roles)) (result : Match roles) :
 result ∈ positive probe entries ↔
 ∃ plan ∈ entries, probe plan = some true ∧ observation plan = result := by
 simp only [positive,List.mem_map,List.mem_filter,beq_iff_eq]
 constructor
 · rintro ⟨p,⟨inside,h⟩,same⟩
   exact ⟨p,inside,h,same⟩
 · rintro ⟨p,inside,h,same⟩
   exact ⟨p,⟨inside,h⟩,same⟩

theorem unresolved_exact (probe : Plan roles → Option Bool) (entries : List (Plan roles)) (plan : Plan roles) :
 plan ∈ unresolved probe entries ↔ plan ∈ entries ∧ probe plan = none := by
 simp [unresolved]

theorem source_sound (registry : Registry) (state : State roles) (root focus : Occurrence roles)
 (checked : (Boundary roles).Checked registry) (metadata : Metadata (Encoded registry) state.core.erased.current.context)
 (probe : Plan roles → Option Bool)
 (honest : Honest probe (atFocus (Encoded registry) state root focus (declChecked checked)))
 (member : (key,kids) ∈ positive probe (atFocus (Encoded registry) state root focus (declChecked checked))) :
 Survivor (Encoded registry) state.core.erased.current.context focus key kids := by
 obtain ⟨plan,listed,success,seen⟩ := (positive_exact ..).mp member
 obtain ⟨known,same⟩ := (atFocus_exact ..).mp listed
 have real := to_survivor (Encoded registry) state root (declChecked checked) plan known metadata
   (honest.positive plan listed success)
 unfold observation at seen
 rw [Prod.mk.inj seen |>.1,Prod.mk.inj seen |>.2,same] at real
 exact real

theorem source_complete_or_unknown (registry : Registry) (state : State roles) (root focus : Occurrence roles)
 (checked : (Boundary roles).Checked registry)
 (reachable : B4TargetV8.Reachable (Boundary roles) registry root state)
 (generated : Generated state.core.erased.current root focus)
 (probe : Plan roles → Option Bool)
 (honest : Honest probe (atFocus (Encoded registry) state root focus (declChecked checked)))
 (actual : Survivor (Encoded registry) state.core.erased.current.context focus key kids) :
 (key,kids) ∈ positive probe (atFocus (Encoded registry) state root focus (declChecked checked)) ∨
 ∃ plan ∈ unresolved probe (atFocus (Encoded registry) state root focus (declChecked checked)),
   observation plan = (key,kids) := by
 obtain ⟨plan,listed,same,keyEq,kidsEq,head⟩ :=
   from_survivor registry state root focus checked reachable generated actual
 have entry := (atFocus_exact (Encoded registry) state root focus (declChecked checked) plan).mpr ⟨listed,same⟩
 have observationEq : observation plan = (key,kids) := Prod.ext keyEq kidsEq
 cases outcome : probe plan with
 | none => exact Or.inr ⟨plan,(unresolved_exact ..).mpr ⟨entry,outcome⟩,observationEq⟩
 | some result =>
   cases result with
   | false => exact False.elim ((honest.negative plan entry outcome) head)
   | true => exact Or.inl ((positive_exact ..).mpr ⟨plan,entry,outcome,observationEq⟩)

end Yulang.GeneralRebaseHeadProbe267
