import Yulang.GeneralRebaseConcreteDriver267

namespace Yulang.GeneralRebaseConcreteCorrect267
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedJournal232 (State)
open GeneralSourceState (Output)
open GeneralRebaseSourceSurvivor267 (Boundary)
open GeneralRebaseSourceObserver267 (Probes)
open GeneralRebaseObserverCoverage267 (Covers)
open GeneralRebaseObserverExact267 (observe source_relative_terminal)
open GeneralRebaseLiveProjection264 (project)
open GeneralRebaseDynamicTrace267 (Trace decision)
open GeneralRebaseDynamicRun267 (StableProjection)
open GeneralRebaseConcreteNext267 (next commutes success_decision decreases)
open GeneralRebaseConcreteDriver267 (drive PathFrom SoundFrom)

theorem verified (registry : Registry) (root : Occurrence roles) (start : State roles)
 (checked : (Boundary roles).Checked registry) (initial : (Boundary roles).Initial registry root start)
 (probeFamily : State roles → Probes roles) (sound : SoundFrom registry root start checked probeFamily)
 (complete : ∀ state, PathFrom registry root start state → Covers registry state root checked (probeFamily state))
 (owners : List Nat) (pool : List Output)
 (closed : ∀ state, PathFrom registry root start state →
  GeneralRebaseClosedObserver259.Closed (observe registry root state checked (probeFamily state) owners pool))
 (state : State roles) (path : PathFrom registry root start state) :
 ∃ last count,
 drive registry root start checked initial probeFamily sound owners pool state path = .ok (count,last) ∧
 Trace registry root checked probeFamily owners pool count state last ∧
 StableProjection registry root owners pool last := by
 generalize rankEq : (project owners pool state).remaining.length = k
 induction k using Nat.strongRecOn generalizing state with
 | ind k recur =>
   let reachable : B4TargetV8.Reachable (Boundary roles) registry root state := ⟨start,initial,path⟩
   have commute := commutes registry root checked probeFamily owners pool state reachable (sound state path)
   rw [drive]
   split
   · rename_i missing failed
     have error : decision registry root checked probeFamily owners pool state = .error missing := by
       rw [←commute,failed]; rfl
     exact False.elim (GeneralRebaseClosedObserver259.next_no_error _ (closed state path) _ missing error)
   · rename_i halted
     have done : decision registry root checked probeFamily owners pool state = .ok none := by
       rw [←commute,halted]; rfl
     have stable := (source_relative_terminal registry root state checked reachable (probeFamily state)
       (sound state path) (complete state path) owners pool).mp (GeneralRebaseScheduler259.terminal _ _ done)
     exact ⟨state,0,rfl,.nil _,stable⟩
   · rename_i entry advanced
     have smaller := decreases registry root checked probeFamily owners pool state reachable (sound state path) advanced
     rw [rankEq] at smaller
     obtain ⟨last,count,successful,trace,quiet⟩ :=
       recur _ smaller entry.after (.tail path entry.step) rfl
     rw [successful]
     exact ⟨last,count+1,rfl,.cons entry.step
       (success_decision registry root checked probeFamily owners pool state reachable _ advanced) trace,quiet⟩

/-- A source-derived closed support makes the checked implementation finish
successfully with an actual path of the reported strict length. The executable
semantic probes and uniform soundness/completeness still have to be provided. -/
theorem on_source (registry : Registry) (root : Occurrence roles) (start : State roles)
 (checked : (Boundary roles).Checked registry) (initial : (Boundary roles).Initial registry root start)
 (probeFamily : State roles → Probes roles) (sound : SoundFrom registry root start checked probeFamily)
 (complete : ∀ state, PathFrom registry root start state → Covers registry state root checked (probeFamily state)) :
 ∃ (owners : List Nat) (pool : List Output) (last : State roles) (count : Nat),
 drive registry root start checked initial probeFamily sound owners pool start .refl = .ok (count,last) ∧
 Trace registry root checked probeFamily owners pool count start last ∧
 StableProjection registry root owners pool last ∧
 count + (project owners pool last).remaining.length ≤ (project owners pool start).remaining.length := by
 obtain ⟨owners,pool,closed⟩ := GeneralRebaseObserverExact267.source_basis registry root start checked initial
 obtain ⟨last,count,result,trace,terminal⟩ := verified registry root start checked initial probeFamily sound complete
   owners pool (fun state h => closed state h (probeFamily state) (sound state h)) start .refl
 exact ⟨owners,pool,last,count,result,trace,terminal,GeneralRebaseDynamicTrace267.budget _ _ _ _ _ _ trace⟩

end Yulang.GeneralRebaseConcreteCorrect267
