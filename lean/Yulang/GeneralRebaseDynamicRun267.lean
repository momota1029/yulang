import Yulang.GeneralRebaseDynamicTrace267

namespace Yulang.GeneralRebaseDynamicRun267
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedJournal232 (State)
open GeneralSourceState (Output)
open GeneralRebaseSourceSurvivor267 (Boundary)
open GeneralRebaseSourceObserver267 (Probes)
open GeneralRebaseLiveProjection264 (project)
open GeneralRebaseObserverCoverage267 (Covers)
open GeneralRebaseObserverSound267 (Sound)
open GeneralRebaseObserverExact267 (observe step_iff source_relative_terminal)
open GeneralRebaseDynamicTrace267 (Trace decision)

def StableProjection (registry : Registry) (root : Occurrence roles) (owners : List Nat) (pool : List Output)
 (state : State roles) : Prop :=
 ∀ after, (Boundary roles).Step registry root state after →
 project owners pool after = project owners pool state

theorem from_closed_basis (registry : Registry) (root : Occurrence roles) (start : State roles)
 (checked : (Boundary roles).Checked registry) (initial : (Boundary roles).Initial registry root start)
 (probeFamily : State roles → Probes roles)
 (sound : ∀ state, B4Target.Steps ((Boundary roles).Step registry root) start state →
   Sound registry state root checked (probeFamily state))
 (proper : ∀ state, B4Target.Steps ((Boundary roles).Step registry root) start state →
   Covers registry state root checked (probeFamily state))
 (owners : List Nat) (pool : List Output)
 (closed : ∀ state, B4Target.Steps ((Boundary roles).Step registry root) start state →
   GeneralRebaseClosedObserver259.Closed (observe registry root state checked (probeFamily state) owners pool))
 (state : State roles) (prior : B4Target.Steps ((Boundary roles).Step registry root) start state) :
 ∃ last count, Trace registry root checked probeFamily owners pool count state last ∧
   StableProjection registry root owners pool last ∧
   decision registry root checked probeFamily owners pool last = .ok none := by
 generalize rankEq : (project owners pool state).remaining.length = k
 induction k using Nat.strongRecOn generalizing state with
 | ind k recur =>
   have reachable : B4TargetV8.Reachable (Boundary roles) registry root state := ⟨start,initial,prior⟩
   cases h : decision registry root checked probeFamily owners pool state with
   | error missing =>
     exact False.elim (GeneralRebaseClosedObserver259.next_no_error _ (closed state prior) _ missing h)
   | ok found =>
     cases found with
     | none =>
       have quiet := GeneralRebaseScheduler259.terminal _ _ h
       exact ⟨state,0,.nil _,(source_relative_terminal registry root state checked reachable
         (probeFamily state) (sound state prior) (proper state prior) owners pool).mp quiet,h⟩
     | some target =>
       have finite := GeneralRebaseScheduler259.next_step _ _ _ h
       obtain ⟨after,actual,ends,_⟩ :=
         (step_iff registry root state checked reachable (probeFamily state)
           (sound state prior) (proper state prior) owners pool target).mp finite
       have decrease := GeneralRebaseStep258.decreases _ finite
       rw [←ends,rankEq] at decrease
       obtain ⟨last,m,rest,quiet,done⟩ := recur _ decrease after (.tail prior actual) rfl
       exact ⟨last,m+1,.cons actual (ends.symm ▸ h) rest,quiet,done⟩

/-- Conditional end-to-end dynamic replay with the executable checked next
called at each concrete state. This theorem constructs existence of source
witnesses, not an executable selector for concrete representatives. -/
theorem completes (registry : Registry) (root : Occurrence roles) (start : State roles)
 (checked : (Boundary roles).Checked registry) (initial : (Boundary roles).Initial registry root start)
 (probeFamily : State roles → Probes roles)
 (sound : ∀ state, B4Target.Steps ((Boundary roles).Step registry root) start state →
   Sound registry state root checked (probeFamily state))
 (proper : ∀ state, B4Target.Steps ((Boundary roles).Step registry root) start state →
   Covers registry state root checked (probeFamily state)) :
 ∃ (owners : List Nat) (pool : List Output) (last : State roles) (count : Nat),
 Trace registry root checked probeFamily owners pool count start last ∧
 StableProjection registry root owners pool last ∧
 decision registry root checked probeFamily owners pool last = .ok none ∧
 count + (project owners pool last).remaining.length ≤ (project owners pool start).remaining.length := by
 obtain ⟨owners,pool,closed⟩ := GeneralRebaseObserverExact267.source_basis registry root start checked initial
 obtain ⟨last,count,trace,quiet,halt⟩ := from_closed_basis registry root start checked initial probeFamily sound proper
   owners pool (fun state prior => closed state prior (probeFamily state) (sound state prior)) start .refl
 exact ⟨owners,pool,last,count,trace,quiet,halt,GeneralRebaseDynamicTrace267.budget _ _ _ _ _ _ trace⟩

end Yulang.GeneralRebaseDynamicRun267
