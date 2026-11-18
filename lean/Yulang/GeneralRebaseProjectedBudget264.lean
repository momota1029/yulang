import Yulang.GeneralRebaseSourceProjection264
namespace Yulang.GeneralRebaseProjectedBudget264
open GeneralRebaseLiveProjection264 (SourceState project liveFacts)
open GeneralSourceState (Output)

/-- Count strict projected changes, retaining every source step in the trace.
A stuttering source step contributes zero, not a fictitious termination proof. -/
inductive Trace (owners : List Nat) (pool : List Output)
 (registry : GeneralDeclarations.Registry) (root : GeneralSourceDictionaries.Occurrence roles) :
 Nat → SourceState roles → SourceState roles → Prop where
 | refl (state) : Trace owners pool registry root 0 state state
 | stutter {count first middle last} : Trace owners pool registry root count first middle →
   GeneralNominalVersionedMixedKernel234.Step registry root middle last →
   project owners pool last = project owners pool middle → Trace owners pool registry root count first last
 | advance {count first middle last} : Trace owners pool registry root count first middle →
   GeneralNominalVersionedMixedKernel234.Step registry root middle last →
   project owners pool last ≠ project owners pool middle → Trace owners pool registry root (count+1) first last

theorem from_steps (owners : List Nat) (pool : List Output)
 {registry : GeneralDeclarations.Registry} {root : GeneralSourceDictionaries.Occurrence roles}
 {first last : SourceState roles}
 (path : B4Target.Steps (GeneralNominalVersionedMixedKernel234.Step registry root) first last) :
 ∃ count, Trace owners pool registry root count first last := by
 classical
 induction path with
 | refl => exact ⟨0,.refl _⟩
 | @tail middle last path step ih =>
   obtain ⟨count,prior⟩ := ih
   by_cases same : project owners pool last = project owners pool middle
   · exact ⟨count,.stutter prior step same⟩
   · exact ⟨count+1,.advance prior step same⟩

theorem to_steps {owners : List Nat} {pool : List Output}
 {registry : GeneralDeclarations.Registry} {root : GeneralSourceDictionaries.Occurrence roles}
 {count : Nat} {first last : SourceState roles} (trace : Trace owners pool registry root count first last) :
 B4Target.Steps (GeneralNominalVersionedMixedKernel234.Step registry root) first last := by
 induction trace with
 | refl => exact .refl
 | stutter _ step _ ih => exact .tail ih step
 | advance _ step _ ih => exact .tail ih step

theorem budget_remaining {owners : List Nat} {pool : List Output}
 {registry : GeneralDeclarations.Registry} {root : GeneralSourceDictionaries.Occurrence roles}
 {count : Nat} {first last : SourceState roles} (trace : Trace owners pool registry root count first last) :
 count + (project owners pool last).remaining.length ≤ (project owners pool first).remaining.length := by
 induction trace with
 | refl => omega
 | stutter _ _ same ih => simpa only [same] using ih
 | advance _ step changed ih =>
   have decrease := GeneralRebaseSourceProjection264.strict_decrease owners pool step changed
   omega

theorem budget {owners : List Nat} {pool : List Output}
 {registry : GeneralDeclarations.Registry} {root : GeneralSourceDictionaries.Occurrence roles}
 {count : Nat} {first last : SourceState roles} (trace : Trace owners pool registry root count first last) :
 count ≤ owners.length * (pool.length + pool.length * pool.length) := by
 have remaining := budget_remaining trace
 have size := (project owners pool first).canonical.length_le
 have bound := GeneralRebaseUniversalBasis263.basis_bound owners pool
 omega

/-- Source formation provides one basis for the entire reachable family.
Every finite source path has a bounded number of strictly changed projections;
its number of stuttering steps is deliberately unrestricted. -/
theorem source_tracks (registry : GeneralDeclarations.Registry)
 (root : GeneralSourceDictionaries.Occurrence roles) (start : SourceState roles)
 (source : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Initial registry root start) :
 ∃ owners : List Nat, ∃ pool : List Output, ∀ state,
 B4Target.Steps ((GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Step registry root) start state →
 liveFacts state ⊆ GeneralRebaseUniversalBasis263.basis owners pool ∧
 ∃ count, Trace owners pool (GeneralNominalCenteredHeadAllocEncoding.registry registry) root count start state ∧
 count ≤ owners.length * (pool.length + pool.length * pool.length) := by
 obtain ⟨owners,pool,covered⟩ := GeneralRebaseLiveProjection264.source_covered registry root start source
 refine ⟨owners,pool,?_⟩
 intro state path
 obtain ⟨count,trace⟩ := from_steps owners pool path
 exact ⟨covered state path,count,trace,budget trace⟩
end Yulang.GeneralRebaseProjectedBudget264
