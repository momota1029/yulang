import Yulang.GeneralRebaseObserverExact267
import Yulang.GeneralRebaseCertifiedSteps266

namespace Yulang.GeneralRebaseDynamicTrace267
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedJournal232 (State)
open GeneralSourceState (Output)
open GeneralRebaseSourceSurvivor267 (Boundary)
open GeneralRebaseSourceObserver267 (Probes)
open GeneralRebaseLiveProjection264 (project)
open GeneralRebaseObserverExact267 (observe)
open GeneralRebaseScheduler259 (next next_step)

def decision (registry : Registry) (root : Occurrence roles) (checked : (Boundary roles).Checked registry)
 (probeFamily : State roles → Probes roles) (owners : List Nat) (pool : List Output) (state : State roles) :
 Except (List GeneralRebaseStep258.Fact) (Option (GeneralRebaseStep258.State (GeneralRebaseCompression266.Basis owners pool))) :=
 next (observe registry root state checked (probeFamily state) owners pool) (project owners pool state)

/-- At each step the computation uses the current concrete representative,
not the initial observer reused at its abstract successor. -/
inductive Trace (registry : Registry) (root : Occurrence roles) (checked : (Boundary roles).Checked registry)
 (probeFamily : State roles → Probes roles) (owners : List Nat) (pool : List Output) :
 Nat → State roles → State roles → Prop where
 | nil (state) : Trace registry root checked probeFamily owners pool 0 state state
 | cons : (Boundary roles).Step registry root first middle →
   decision registry root checked probeFamily owners pool first = .ok (some (project owners pool middle)) →
   Trace registry root checked probeFamily owners pool n middle last →
   Trace registry root checked probeFamily owners pool (n+1) first last

theorem budget (registry : Registry) (root : Occurrence roles) (checked : (Boundary roles).Checked registry)
 (probeFamily : State roles → Probes roles) (owners : List Nat) (pool : List Output)
 (trace : Trace registry root checked probeFamily owners pool n first last) :
 n + (project owners pool last).remaining.length ≤ (project owners pool first).remaining.length := by
 induction trace with
 | nil _ => simp
 | cons _ found _ ih =>
   have finite := next_step _ _ _ found
   have decreased := GeneralRebaseStep258.decreases _ finite
   omega

theorem old_steps (registry : Registry) (root : Occurrence roles) (checked : (Boundary roles).Checked registry)
 (probeFamily : State roles → Probes roles) (owners : List Nat) (pool : List Output)
 (trace : Trace registry root checked probeFamily owners pool n first last) :
 B4Target.Steps ((Boundary roles).Step registry root) first last := by
 induction trace with
 | nil _ => exact .refl
 | cons first _ _ ih => exact GeneralRebaseCertifiedSteps266.prepend first ih

end Yulang.GeneralRebaseDynamicTrace267
