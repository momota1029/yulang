import Yulang.GeneralRebaseLiveProjection264
import Yulang.GeneralRebaseUniversalMeaning263
import Yulang.GeneralNominalVersionedMixedPlanLedger235
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseLiveMeaning264
open GeneralNominalCenters (Plan)
open GeneralSourceState (Output)
open GeneralNominalCommonBridge (Assignment)
open GeneralRebaseMultiSelection263 (ofPlan proposal requests)
open GeneralRebaseLiveProjection264 (SourceState liveFacts facts project)

def Live (source : SourceState roles) (assignment : Assignment) : Prop :=
 ∀ plan ∈ source.plans,
 GeneralNominalVersionedEffects231.ClassEffects source.core plan.packet.site.occurrence plan assignment

/-- The original non-live remainder is retained explicitly. In particular,
historical bodies and the legacy journal have not been finitely compressed. -/
def Remainder (source : SourceState roles) (assignment : Assignment) : Prop :=
 GeneralNominalVersionedJournal232.Legacy.Models source.legacy assignment ∧
 (∀ plan ∈ source.plans, GeneralNominalVersionedPlans231.Holds plan assignment) ∧
 ∀ effect ∈ source.effects, effect.Holds assignment

theorem journal_exact (source : SourceState roles)
 (synced : GeneralNominalVersionedMixedPlanLedger235.Synced source) (assignment : Assignment) :
 GeneralNominalVersionedJournal232.Models source assignment ↔ Remainder source assignment ∧ Live source assignment := by
 constructor
 · rintro ⟨legacy,plans,effects⟩
   refine ⟨⟨legacy,plans,fun effect member => (effects effect member).1⟩,?_⟩
   intro plan member
   rw [synced] at member
   obtain ⟨effect,present,rfl⟩ := List.mem_map.mp member
   exact (effects effect present).2
 · rintro ⟨⟨legacy,plans,historical⟩,live⟩
   refine ⟨legacy,plans,?_⟩
   intro effect member
   refine ⟨historical effect member,?_⟩
   apply live effect.plan
   rw [synced]
   exact List.mem_map.mpr ⟨effect,member,rfl⟩

theorem live_facts_exact (owners : List Nat) (representative : Nat → Plan roles)
 (source : SourceState roles)
 (listed : ∀ plan ∈ source.plans, (ofPlan plan).owner ∈ owners)
 (assignment : Assignment)
 (compatible : ∀ plan ∈ source.plans,
 GeneralRebaseNormalizedBody263.Compatible (representative (ofPlan plan).owner) plan assignment) :
 (∀ fact ∈ liveFacts source, GeneralRebaseOwnerTable263.Holds owners representative assignment fact) ↔
 Live source assignment := by
 constructor
 · intro valid plan member
   have holds : ∀ fact ∈ proposal source.core (ofPlan plan),
       GeneralRebaseOwnerTable263.Holds owners representative assignment fact :=
     fun fact included => valid fact (List.mem_flatMap.mpr ⟨plan,member,included⟩)
   have meaning := (GeneralRebaseUniversalMeaning263.actual_proposal owners representative (ofPlan plan).owner
     (listed plan member) plan (requests source.core (ofPlan plan)) assignment (compatible plan member)).mp holds
   simpa only [requests,ofPlan,GeneralRebaseExecutableRequests262.requests_eq,GeneralRebaseClassTable261.Effects,GeneralNominalVersionedEffects231.ClassEffects,GeneralNominalCenteredHeadOutputs.EqualOutputs] using meaning
 · intro live fact included
   obtain ⟨plan,member,present⟩ := List.mem_flatMap.mp included
   apply (GeneralRebaseUniversalMeaning263.actual_proposal owners representative (ofPlan plan).owner
     (listed plan member) plan (requests source.core (ofPlan plan)) assignment (compatible plan member)).mpr _ fact present
   simpa only [requests,ofPlan,GeneralRebaseExecutableRequests262.requests_eq,GeneralRebaseClassTable261.Effects,GeneralNominalVersionedEffects231.ClassEffects,GeneralNominalCenteredHeadOutputs.EqualOutputs] using live plan member

theorem project_models (base : Assignment → Prop) (owners : List Nat) (representative : Nat → Plan roles)
 (pool : List Output) (source : SourceState roles)
 (listed : ∀ plan ∈ source.plans, (ofPlan plan).owner ∈ owners)
 (coverage : GeneralRebaseChildRequestPool262.Covered source.core pool)
 (compatible : ∀ assignment, base assignment → ∀ plan ∈ source.plans,
 GeneralRebaseNormalizedBody263.Compatible (representative (ofPlan plan).owner) plan assignment)
 (assignment : Assignment) :
 GeneralRebaseUniversalMeaning263.Models base owners representative (project owners pool source) assignment ↔
 base assignment ∧ Live source assignment := by
 unfold GeneralRebaseUniversalMeaning263.Models project
 rw [GeneralRebaseFactSemantics259.write_exact,GeneralRebaseFactSemantics259.initial_exact]
 constructor
 · rintro ⟨prior,factsValid⟩
   refine ⟨prior,(live_facts_exact owners representative source listed assignment (compatible assignment prior)).mp ?_⟩
   intro fact member
   exact factsValid fact (GeneralRebaseLiveProjection264.covered owners pool source listed coverage member) member
 · rintro ⟨prior,live⟩
   refine ⟨prior,?_⟩
   intro fact _ member
   exact (live_facts_exact owners representative source listed assignment (compatible assignment prior)).mpr live fact member

/-- Exact re-encoding of the live slice, retaining the original non-live
remainder and an explicit fixed-representative compatibility premise. -/
theorem project_journal (owners : List Nat) (representative : Nat → Plan roles)
 (pool : List Output) (source : SourceState roles)
 (synced : GeneralNominalVersionedMixedPlanLedger235.Synced source)
 (listed : ∀ plan ∈ source.plans, (ofPlan plan).owner ∈ owners)
 (coverage : GeneralRebaseChildRequestPool262.Covered source.core pool)
 (compatible : ∀ assignment, Remainder source assignment → ∀ plan ∈ source.plans,
 GeneralRebaseNormalizedBody263.Compatible (representative (ofPlan plan).owner) plan assignment)
 (assignment : Assignment) :
 GeneralRebaseUniversalMeaning263.Models (Remainder source) owners representative (project owners pool source) assignment ↔
 GeneralNominalVersionedJournal232.Models source assignment :=
 (project_models (Remainder source) owners representative pool source listed coverage compatible assignment).trans
   (journal_exact source synced assignment).symm
end Yulang.GeneralRebaseLiveMeaning264
