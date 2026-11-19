import Yulang.GeneralRebaseConcreteScan267

namespace Yulang.GeneralRebaseConcreteNext267
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedJournal232 (State)
open GeneralSourceState (Output)
open GeneralRebaseStep258 (Fact)
open GeneralRebaseSourceSurvivor267 (Boundary)
open GeneralRebaseSourceObserver267 (Probes)
open GeneralRebaseObserverSound267 (Sound)
open GeneralRebaseObserverExact267 (observe_current)
open GeneralRebaseDynamicTrace267 (decision)
open GeneralRebaseConcreteEntries267 (Entry entries)
open GeneralRebaseConcreteScan267 (scan abstractResult scan_commutes)
open GeneralRebaseLiveProjection264 (project)

def next (registry : Registry) (root : Occurrence roles) (checked : (Boundary roles).Checked registry)
 (probeFamily : State roles → Probes roles) (owners : List Nat) (pool : List Output) (state : State roles)
 (reachable : B4TargetV8.Reachable (Boundary roles) registry root state)
 (sound : Sound registry state root checked (probeFamily state)) :
 Except (List Fact) (Option (Entry registry root state)) :=
 scan owners pool state (entries registry root state checked reachable (probeFamily state) sound)

theorem commutes (registry : Registry) (root : Occurrence roles) (checked : (Boundary roles).Checked registry)
 (probeFamily : State roles → Probes roles) (owners : List Nat) (pool : List Output) (state : State roles)
 (reachable : B4TargetV8.Reachable (Boundary roles) registry root state)
 (sound : Sound registry state root checked (probeFamily state)) :
 abstractResult owners pool state (next registry root checked probeFamily owners pool state reachable sound) =
 decision registry root checked probeFamily owners pool state := by
 unfold next decision GeneralRebaseScheduler259.next
 rw [scan_commutes,GeneralRebaseConcreteEntries267.same_order,observe_current]

theorem success_decision (registry : Registry) (root : Occurrence roles) (checked : (Boundary roles).Checked registry)
 (probeFamily : State roles → Probes roles) (owners : List Nat) (pool : List Output) (state : State roles)
 (reachable : B4TargetV8.Reachable (Boundary roles) registry root state)
 (sound : Sound registry state root checked (probeFamily state))
 {choice : Entry registry root state}
 (found : next registry root checked probeFamily owners pool state reachable sound = .ok (some choice)) :
 decision registry root checked probeFamily owners pool state = .ok (some (project owners pool choice.after)) := by
 rw [←commutes registry root checked probeFamily owners pool state reachable sound,found]
 rfl

theorem decreases (registry : Registry) (root : Occurrence roles) (checked : (Boundary roles).Checked registry)
 (probeFamily : State roles → Probes roles) (owners : List Nat) (pool : List Output) (state : State roles)
 (reachable : B4TargetV8.Reachable (Boundary roles) registry root state)
 (sound : Sound registry state root checked (probeFamily state))
 {choice : Entry registry root state}
 (found : next registry root checked probeFamily owners pool state reachable sound = .ok (some choice)) :
 (project owners pool choice.after).remaining.length < (project owners pool state).remaining.length :=
 GeneralRebaseStep258.decreases _ (GeneralRebaseScheduler259.next_step _ _ _
    (success_decision registry root checked probeFamily owners pool state reachable sound found))

end Yulang.GeneralRebaseConcreteNext267
