import Yulang.GeneralRebaseDynamicTrace267

namespace Yulang.GeneralRebaseStrictAccessibility267
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralSourceState (Output)
open GeneralRebaseSourceSurvivor267 (Boundary)
open GeneralRebaseLiveProjection264 (project)
open GeneralRebaseSourceObserver267 (Probes)

def Strict (registry : Registry) (root : Occurrence roles) (owners : List Nat) (pool : List Output)
 (after before : State roles) : Prop :=
 (Boundary roles).Step registry root before after ∧ project owners pool after ≠ project owners pool before

/-- Unconditional accessibility for the strict projected subrelation.
The concrete rule is not erased: each certified move is still an actual
source Step. Old source accessibility including stutters is not asserted. -/
theorem wellFounded (registry : Registry) (root : Occurrence roles) (owners : List Nat) (pool : List Output) :
 WellFounded (Strict registry root owners pool) := by
 let rank := fun source : State roles => (project owners pool source).remaining.length
 apply Subrelation.wf (r := InvImage Nat.lt rank) _ (InvImage.wf rank Nat.lt_wfRel.wf)
 intro after before step
 exact GeneralRebaseSourceProjection264.strict_decrease owners pool step.1 step.2

theorem accessible (registry : Registry) (root : Occurrence roles) (owners : List Nat) (pool : List Output)
 (state : State roles) : Acc (Strict registry root owners pool) state :=
 (wellFounded registry root owners pool).apply state

theorem trace_models (registry : Registry) (root : Occurrence roles) (checked : (Boundary roles).Checked registry)
 (probeFamily : State roles → Probes roles) (owners : List Nat) (pool : List Output)
 (trace : GeneralRebaseDynamicTrace267.Trace registry root checked probeFamily owners pool count first last)
 (valid : Models last model) : Models first model :=
 GeneralNominalVersionedMixedKernel234.steps_models
   (GeneralRebaseDynamicTrace267.old_steps _ _ _ _ _ _ trace) valid

end Yulang.GeneralRebaseStrictAccessibility267
