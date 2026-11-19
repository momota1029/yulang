import Yulang.GeneralRebaseConcreteNext267

namespace Yulang.GeneralRebaseConcreteDriver267
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedJournal232 (State)
open GeneralSourceState (Output)
open GeneralRebaseStep258 (Fact)
open GeneralRebaseSourceSurvivor267 (Boundary)
open GeneralRebaseSourceObserver267 (Probes)
open GeneralRebaseObserverSound267 (Sound)
open GeneralRebaseLiveProjection264 (project)
open GeneralRebaseConcreteNext267 (next decreases)

abbrev PathFrom (registry : Registry) (root : Occurrence roles) (start : State roles) :=
 B4Target.Steps ((Boundary roles).Step registry root) start

abbrev SoundFrom (registry : Registry) (root : Occurrence roles) (start : State roles)
 (checked : (Boundary roles).Checked registry) (probeFamily : State roles → Probes roles) :=
 ∀ state, PathFrom registry root start state → Sound registry state root checked (probeFamily state)

/-- A computable driver *relative to the supplied executable probes*.
A selected entry retains the concrete successor, so recursion does not use
choice or attempt to reconstruct source state from the finite projection. -/
def drive (registry : Registry) (root : Occurrence roles) (start : State roles)
 (checked : (Boundary roles).Checked registry) (initial : (Boundary roles).Initial registry root start)
 (probeFamily : State roles → Probes roles) (sound : SoundFrom registry root start checked probeFamily)
 (owners : List Nat) (pool : List Output) (state : State roles) (path : PathFrom registry root start state) :
 Except (List Fact) (Nat × State roles) :=
 match h : next registry root checked probeFamily owners pool state ⟨start,initial,path⟩ (sound state path) with
 | .error missing => .error missing
 | .ok none => .ok (0,state)
 | .ok (some entry) =>
   (drive registry root start checked initial probeFamily sound owners pool entry.after (.tail path entry.step)).map
    (fun result => (result.1+1,result.2))
termination_by (project owners pool state).remaining.length
decreasing_by
 exact decreases registry root checked probeFamily owners pool state ⟨start,initial,path⟩ (sound state path) h

end Yulang.GeneralRebaseConcreteDriver267
