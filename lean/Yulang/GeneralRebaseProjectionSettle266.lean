import Yulang.GeneralRebaseProjectionLift266
import Yulang.GeneralRebaseClosedObserver259

namespace Yulang.GeneralRebaseProjectionSettle266
open GeneralRebaseStep258
open GeneralRebaseBudget258 (Runs)
open GeneralRebaseSettle259 (settle)
open GeneralRebaseCompression266 (Basis)
open GeneralRebaseProjectionObserver266 (Witness observe observe_mem step_exact)
open GeneralRebaseProjectionLift266 (Liftable)
open GeneralRebaseProjectedBudget264 (Trace)
open GeneralRebaseLiveProjection264 (SourceState project)
open GeneralSourceState (Output)

theorem closed (owners : List Nat) (pool : List Output)
 (registry : GeneralDeclarations.Registry) (root : GeneralSourceDictionaries.Occurrence roles) :
 GeneralRebaseClosedObserver259.Closed (observe owners pool registry root) := by
 intro state proposal presentProposal fact member
 obtain ⟨_,_,_,rfl⟩ := (observe_mem owners pool registry root state proposal).mp presentProposal
 exact ((GeneralRebaseFactSemantics259.present_iff _ fact).mp member).1

theorem observer_bound (owners : List Nat) (pool : List Output)
 (registry : GeneralDeclarations.Registry) (root : GeneralSourceDictionaries.Occurrence roles)
 (state : State (Basis owners pool)) :
 (observe owners pool registry root state).length ≤ 2 ^ (Basis owners pool).length := by
 classical
 unfold observe
 rw [List.length_map,← GeneralRebaseFiniteStates263.length]
 exact List.length_filter_le _ _

theorem terminal_iff (owners : List Nat) (pool : List Output)
 (registry : GeneralDeclarations.Registry) (root : GeneralSourceDictionaries.Occurrence roles)
 (state : State (Basis owners pool)) :
 (∀ after, ¬ Step (observe owners pool registry root) state after) ↔
 (∀ after, Witness owners pool registry root state after → after = state) := by
 constructor
 · intro stopped after witnessed
   by_cases equal : after = state
   · exact equal
   · exact False.elim (stopped after ((step_exact owners pool registry root state after).mpr ⟨witnessed,equal⟩))
 · intro flat after advancing
   obtain ⟨witnessed,different⟩ := (step_exact owners pool registry root state after).mp advancing
   exact different (flat after witnessed)

/-- The semantic observer is finite and has a bounded terminal computation as
a mathematical specification; evaluating its classical choices is not claimed. -/
theorem completes (owners : List Nat) (pool : List Output)
 (registry : GeneralDeclarations.Registry) (root : GeneralSourceDictionaries.Occurrence roles)
 (state : State (Basis owners pool)) :
 ∃ final count,
   settle (observe owners pool registry root) state = .ok final ∧
   Runs (observe owners pool registry root) count state final ∧ count ≤ state.remaining.length ∧
   (∀ after, Witness owners pool registry root final after → after = final) := by
 obtain ⟨final,count,success,runs,bound,quiet⟩ := GeneralRebaseClosedObserver259.completion
    (observe owners pool registry root) (closed owners pool registry root) state
 exact ⟨final,count,success,runs,bound,(terminal_iff owners pool registry root final).mp quiet⟩

theorem completes_and_lifts (owners : List Nat) (pool : List Output)
 {registry : GeneralDeclarations.Registry} {root : GeneralSourceDictionaries.Occurrence roles}
 {start : SourceState roles} (localLift : Liftable owners pool registry root start) :
 ∃ terminal count, Trace owners pool registry root count start terminal ∧
   settle (observe owners pool registry root) (project owners pool start) = .ok (project owners pool terminal) ∧
   count ≤ (project owners pool start).remaining.length ∧
   (∀ after, GeneralNominalVersionedMixedKernel234.Step registry root terminal after →
     project owners pool after = project owners pool terminal) := by
 obtain ⟨final,count,success,runs,bound,quiet⟩ := completes owners pool registry root (project owners pool start)
 obtain ⟨terminal,lifted,equal⟩ := GeneralRebaseProjectionLift266.replay_start owners pool localLift runs
 refine ⟨terminal,count,lifted,equal.symm ▸ success,bound,?_⟩
 intro after step
 rw [equal]
 exact quiet _ ⟨terminal,after,step,equal,rfl⟩

end Yulang.GeneralRebaseProjectionSettle266
