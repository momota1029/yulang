import Yulang.GeneralRebaseStutterKeys268

namespace Yulang.GeneralRebaseKeyedWeakObserver268
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedJournal232 (State)
open GeneralSourceState (Output)
open GeneralRebaseLiveProjection264 (project)
open GeneralRebaseCompression266 (Basis)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralRebaseWeakProgress268 (Weak lull_same)
open GeneralRebaseStutterKeys268 (Keys Valid visit visit_exact region_after_lull)
open GeneralRebaseStep258 (Proposal Observer write state_ext)

def proposals (k : Keys n roles) (offers : Fin n → List Proposal) (source : State roles) :
 List Proposal := (visit k source).flatMap offers

/-- Neither an aggregate union of observations nor strict coverage at one
representative suffices: every lifted representative must satisfy soundness. -/
structure Contract (registry : Registry) (root : Occurrence roles) (owners : List Nat) (pool : List Output)
 (k : Keys n roles) (region : State roles → Prop) (offers : Fin n → List Proposal) : Prop where
 sound : ∀ source, region source → ∀ p ∈ offers (k.key source),
   write (project owners pool source) p ≠ project owners pool source →
   ∃ after, Step registry root source after ∧ project owners pool after = write (project owners pool source) p
 complete : ∀ source after, region source → Step registry root source after →
   project owners pool after ≠ project owners pool source →
   ∃ p ∈ offers (k.key source), project owners pool after = write (project owners pool source) p

def observe (k : Keys n roles) (offers : Fin n → List Proposal) (source : State roles)
 (owners : List Nat) (pool : List Output) : Observer (Basis owners pool) :=
 fun state => if state.remaining = (project owners pool source).remaining then proposals k offers source else []

theorem observe_current (k : Keys n roles) (offers : Fin n → List Proposal) (source : State roles)
 (owners : List Nat) (pool : List Output) :
 observe k offers source owners pool (project owners pool source) = proposals k offers source := by simp [observe]

theorem step_iff (k : Keys n roles) (valid : Valid registry root owners pool k region)
 (offers : Fin n → List Proposal) (contract : Contract registry root owners pool k region offers)
 (source : State roles) (allowed : region source) (target : GeneralRebaseStep258.State (Basis owners pool)) :
 GeneralRebaseStep258.Step (observe k offers source owners pool) (project owners pool source) target ↔
 ∃ after, Weak registry root owners pool source after ∧ project owners pool after = target := by
 constructor
 · rintro ⟨p,listed,ends,diff⟩
   rw [observe_current] at listed
   obtain ⟨key,visited,picked⟩ := List.mem_flatMap.mp listed
   obtain ⟨middle,lull,atKey⟩ := (visit_exact k valid source allowed key).mp visited
   have same := lull_same lull
   have changed : write (project owners pool middle) p ≠ project owners pool middle := by
     rw [same,←ends]
     exact fun h => diff (congrArg GeneralRebaseStep258.State.remaining h)
   obtain ⟨after,edge,exactWrite⟩ :=
     contract.sound middle (region_after_lull k valid lull allowed) p (atKey.symm ▸ picked) changed
   exact ⟨after,⟨middle,lull,edge,exactWrite.symm ▸ changed⟩,
     exactWrite.trans ((congrArg (fun state => write state p) same).trans ends.symm)⟩
 · rintro ⟨after,⟨middle,lull,edge,change⟩,ends⟩
   have same := lull_same lull
   obtain ⟨p,picked,exactWrite⟩ := contract.complete middle after (region_after_lull k valid lull allowed) edge change
   refine ⟨p,?_,ends.symm.trans (exactWrite.trans (congrArg (fun state => write state p) same)),?_⟩
   · rw [observe_current]
     exact List.mem_flatMap.mpr ⟨k.key middle,(visit_exact k valid source allowed _).mpr ⟨middle,lull,rfl⟩,picked⟩
   · exact fun h => change (ends.trans ((state_ext _ _ h).trans same.symm))

theorem terminal_iff (k : Keys n roles) (valid : Valid registry root owners pool k region)
 (offers : Fin n → List Proposal) (contract : Contract registry root owners pool k region offers)
 (source : State roles) (allowed : region source) :
 (∀ target, ¬ GeneralRebaseStep258.Step (observe k offers source owners pool) (project owners pool source) target) ↔
 (∀ after, B4Target.Steps (Step registry root) source after → project owners pool after = project owners pool source) := by
 rw [← GeneralRebaseWeakTerminal268.terminal_iff]
 constructor
 · intro terminal after moved
   exact terminal _ ((step_iff k valid offers contract source allowed _).mpr ⟨after,moved,rfl⟩)
 · intro terminal target moved
   obtain ⟨after,weak,_⟩ := (step_iff k valid offers contract source allowed target).mp moved
   exact terminal after weak

end Yulang.GeneralRebaseKeyedWeakObserver268
