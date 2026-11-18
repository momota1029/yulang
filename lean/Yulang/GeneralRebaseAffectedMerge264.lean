import Yulang.GeneralRebaseMergeRequests264
import Yulang.GeneralRebaseLiveProjection264
namespace Yulang.GeneralRebaseAffectedMerge264
open GeneralNominalCenters (Plan Site)
open GeneralRebaseLiveProjection264 (SourceState liveFacts facts project)
open GeneralRebaseMultiSelection263 (ofPlan proposal requests)
open GeneralNominalSaturationState (Alias)
open GeneralSourceState (Output)
open GeneralRebaseStep258 (Fact write)

def affected (source : SourceState roles) (first last : Site roles) (plan : Plan roles) : Bool :=
 GeneralFiniteAliasSearch262.connected source.core.erased.current.aliases
   plan.packet.site.occurrence.identity first.occurrence.identity ||
 GeneralFiniteAliasSearch262.connected source.core.erased.current.aliases
   plan.packet.site.occurrence.identity last.occurrence.identity

def plans (source : SourceState roles) (first last : Site roles) : List (Plan roles) :=
 source.plans.filter (affected source first last)

theorem affected_exact (source : SourceState roles) (first last : Site roles) (plan : Plan roles) :
 affected source first last plan = true ↔
 Alias source.core.erased.current plan.packet.site.occurrence.identity first.occurrence.identity ∨
 Alias source.core.erased.current plan.packet.site.occurrence.identity last.occurrence.identity := by
 simp only [affected,Bool.or_eq_true,GeneralFiniteAliasSearch262.exact]

theorem unaffected_proposal (source : SourceState roles) (first last : Site roles) (plan : Plan roles)
 (away : affected source first last plan = false) (fact : Fact) :
 fact ∈ proposal (GeneralNominalVersionedAdministrative232.merge source first last).core (ofPlan plan) ↔
 fact ∈ proposal source.core (ofPlan plan) := by
 have outside : ¬ (Alias source.core.erased.current plan.packet.site.occurrence.identity first.occurrence.identity ∨
   Alias source.core.erased.current plan.packet.site.occurrence.identity last.occurrence.identity) := by
  intro inside
  have impossible := (affected_exact source first last plan).mpr inside
  rw [away] at impossible
  cases impossible
 apply GeneralRebaseStableClass261.reordered
 intro output
 simpa only [requests,ofPlan,GeneralRebaseExecutableRequests262.requests_eq] using
   GeneralRebaseMergeRequests264.requests_unaffected source first last plan.packet.site.occurrence
     (fun h => outside (Or.inl h)) (fun h => outside (Or.inr h)) output

/-- Exact set decomposition, not a claim that the request lists are identical. -/
theorem liveFacts_split (source : SourceState roles) (first last : Site roles) (fact : Fact) :
 fact ∈ liveFacts (GeneralNominalVersionedAdministrative232.merge source first last) ↔
 fact ∈ liveFacts source ∨
 fact ∈ facts (GeneralNominalVersionedAdministrative232.merge source first last).core (plans source first last) := by
 constructor
 · intro member
   obtain ⟨plan,registered,present⟩ := List.mem_flatMap.mp member
   by_cases inside : affected source first last plan = true
   · exact Or.inr (List.mem_flatMap.mpr ⟨plan,List.mem_filter.mpr ⟨registered,inside⟩,present⟩)
   · have away : affected source first last plan = false := Bool.eq_false_iff.mpr inside
     exact Or.inl (List.mem_flatMap.mpr ⟨plan,registered,(unaffected_proposal source first last plan away fact).mp present⟩)
 · rintro (prior | changed)
   · apply GeneralRebaseLiveProjection264.monotone source.core _ source.plans source.plans (fun _ h => h) _ prior
     intro plan _ output requested
     simpa only [requests,GeneralRebaseExecutableRequests262.requests_eq] using
       (GeneralRebaseSourceRequests264.merge_growth source first last).requests (ofPlan plan).root output
         (by simpa only [requests,GeneralRebaseExecutableRequests262.requests_eq] using requested)
   · obtain ⟨plan,registered,present⟩ := List.mem_flatMap.mp changed
     exact List.mem_flatMap.mpr ⟨plan,(List.mem_filter.mp registered).1,present⟩

/-- Only Plans in the two pre-merge alias classes need to be rescanned.
The actual merge guards are not weakened or assumed to hold by this equation. -/
theorem project_merge (owners : List Nat) (pool : List Output) (source : SourceState roles) (first last : Site roles) :
 project owners pool (GeneralNominalVersionedAdministrative232.merge source first last) =
 write (project owners pool source)
   (facts (GeneralNominalVersionedAdministrative232.merge source first last).core (plans source first last)) := by
 unfold project
 rw [← GeneralRebaseWriteAlgebra259.append]
 apply GeneralRebaseLiveProjection264.write_members
 intro fact
 rw [liveFacts_split,List.mem_append]

theorem plan_bound (source : SourceState roles) (first last : Site roles) :
 (plans source first last).length ≤ source.plans.length := List.length_filter_le ..
end Yulang.GeneralRebaseAffectedMerge264
