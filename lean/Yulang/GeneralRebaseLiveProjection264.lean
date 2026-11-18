import Yulang.GeneralRebaseUniversalSource263
import Yulang.GeneralRebaseWriteAlgebra259
namespace Yulang.GeneralRebaseLiveProjection264
open GeneralRebaseStep258
open GeneralNominalCenters (Plan)
open GeneralSourceState (Output)
abbrev SourceState := GeneralNominalVersionedJournal232.State
open GeneralRebaseMultiSelection263 (ofPlan proposal requests)

def facts (source : GeneralNominalCenteredSteps.State roles) (plans : List (Plan roles)) : List Fact :=
 plans.flatMap fun plan => proposal source (ofPlan plan)

def liveFacts (source : SourceState roles) : List Fact := facts source.core source.plans

def project (owners : List Nat) (pool : List Output) (source : SourceState roles) :
 GeneralRebaseUniversalObserver263.Current owners pool :=
 write (initial (GeneralRebaseUniversalBasis263.basis owners pool)) (liveFacts source)

theorem member (source : GeneralNominalCenteredSteps.State roles) (plans : List (Plan roles)) (fact : Fact) :
 fact ∈ facts source plans ↔ ∃ plan ∈ plans, fact ∈ proposal source (ofPlan plan) := List.mem_flatMap

theorem monotone (before after : GeneralNominalCenteredSteps.State roles)
 (first last : List (Plan roles)) (retained : first ⊆ last)
 (grown : ∀ plan ∈ first, ∀ output ∈ requests before (ofPlan plan), output ∈ requests after (ofPlan plan)) :
 facts before first ⊆ facts after last := by
 intro fact included
 obtain ⟨plan,registered,present⟩ := (member before first fact).mp included
 apply (member after last fact).mpr
 refine ⟨plan,retained registered,?_⟩
 exact GeneralRebaseStableClass261.monotone plan (ofPlan plan).owner _ _ (grown plan registered) fact present

theorem same_members (before after : GeneralNominalCenteredSteps.State roles)
 (first last : List (Plan roles)) (registered : ∀ plan, plan ∈ first ↔ plan ∈ last)
 (same : ∀ plan ∈ first, ∀ output, output ∈ requests before (ofPlan plan) ↔ output ∈ requests after (ofPlan plan))
 (fact : Fact) : fact ∈ facts before first ↔ fact ∈ facts after last := by
 constructor
 · exact monotone before after first last (fun p h => (registered p).mp h)
     (fun p h o hmem => (same p h o).mp hmem) (a := fact)
 · exact monotone after before last first (fun p h => (registered p).mpr h)
     (fun p h o hmem => (same p ((registered p).mpr h) o).mpr hmem) (a := fact)

theorem write_members {basis : List Fact} (state : GeneralRebaseStep258.State basis)
 (first last : List Fact) (same : ∀ fact, fact ∈ first ↔ fact ∈ last) : write state first = write state last := by
 apply state_ext
 apply List.filter_congr
 intro fact _
 change (!first.contains fact) = (!last.contains fact)
 apply congrArg Bool.not
 exact Bool.eq_iff_iff.mpr (by simpa using same fact)

theorem absorb {basis : List Fact} (state : GeneralRebaseStep258.State basis)
 (first last : List Fact) (included : first ⊆ last) : write (write state first) last = write state last := by
 rw [← GeneralRebaseWriteAlgebra259.append]
 apply write_members
 intro fact
 simp only [List.mem_append]
 exact ⟨fun h => h.elim (fun member => included member) id,Or.inr⟩

/-- This abstraction is not claimed to reconstruct a source state. Coverage
is proved separately, so no out-of-basis live obligation is silently discarded. -/
theorem covered (owners : List Nat) (pool : List Output) (source : SourceState roles)
 (listed : ∀ plan ∈ source.plans, (ofPlan plan).owner ∈ owners)
 (coverage : GeneralRebaseChildRequestPool262.Covered source.core pool) :
 liveFacts source ⊆ GeneralRebaseUniversalBasis263.basis owners pool := by
 intro fact present
 obtain ⟨plan,registered,included⟩ := (member source.core source.plans fact).mp present
 exact GeneralRebaseUniversalBasis263.proposal_covered owners pool plan (ofPlan plan).owner
   (listed plan registered) _ (fun output requested => GeneralRebaseChildRequestPool262.requests_covered source.core pool coverage (ofPlan plan).root output (by simpa only [requests,GeneralRebaseExecutableRequests262.requests_eq] using requested)) included

theorem source_covered (registry : GeneralDeclarations.Registry) (root : GeneralSourceDictionaries.Occurrence roles)
 (start : SourceState roles)
 (source : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Initial registry root start) :
 ∃ owners : List Nat, ∃ pool : List Output, ∀ state,
 B4Target.Steps ((GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Step registry root) start state →
 liveFacts state ⊆ GeneralRebaseUniversalBasis263.basis owners pool := by
 obtain ⟨owners,pool,bounds⟩ := GeneralRebaseMultiSource263.source_bounds registry root start source
 refine ⟨owners,pool,?_⟩
 intro state path
 apply covered owners pool state _ (bounds state path).2
 intro plan registered
 exact (bounds state path).1 (ofPlan plan) (List.mem_map.mpr ⟨plan,registered,rfl⟩)

theorem project_same (owners : List Nat) (pool : List Output) (before after : SourceState roles)
 (same : ∀ fact, fact ∈ liveFacts before ↔ fact ∈ liveFacts after) :
 project owners pool before = project owners pool after := write_members _ _ _ same

/-- Monotone source live facts give an exact rescan square. This may be a
batch, and does not identify the source transition with a single strict write. -/
theorem rescan (owners : List Nat) (pool : List Output) (before after : SourceState roles)
 (included : liveFacts before ⊆ liveFacts after) :
 project owners pool after = write (project owners pool before) (liveFacts after) :=
 (absorb _ _ _ included).symm

theorem rescan_batch (owners : List Nat) (pool : List Output) (before after : SourceState roles)
 (included : liveFacts before ⊆ liveFacts after) :
 project owners pool after = GeneralRebaseWriteAlgebra259.batch (project owners pool before)
   (after.plans.map fun plan => proposal after.core (ofPlan plan)) := by
 rw [GeneralRebaseWriteAlgebra259.batch_exact]
 simpa only [liveFacts,facts,List.flatMap] using rescan owners pool before after included

end Yulang.GeneralRebaseLiveProjection264
