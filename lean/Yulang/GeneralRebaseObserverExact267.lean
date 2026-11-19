import Yulang.GeneralRebaseObserverSound267
import Yulang.GeneralRebaseCompression266

namespace Yulang.GeneralRebaseObserverExact267
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedJournal232 (State)
open GeneralSourceState (Output)
open GeneralRebaseSourceSurvivor267 (Boundary)
open GeneralRebaseSourceObserver267 (Probes proposals)
open GeneralRebaseObserverCoverage267 (Covers)
open GeneralRebaseObserverSound267 (Sound)
open GeneralRebaseLiveProjection264 (project liveFacts)
open GeneralRebaseCompression266 (Basis)

def observe (registry : Registry) (root : Occurrence roles) (source : State roles)
 (checked : (Boundary roles).Checked registry) (probes : Probes roles) (owners : List Nat) (pool : List Output) :
 GeneralRebaseStep258.Observer (Basis owners pool) :=
 fun state =>
  if state.remaining = (project owners pool source).remaining then proposals registry source root checked probes else []

theorem observe_current (registry : Registry) (root : Occurrence roles) (source : State roles)
 (checked : (Boundary roles).Checked registry) (probes : Probes roles) (owners : List Nat) (pool : List Output) :
 observe registry root source checked probes owners pool (project owners pool source) =
 proposals registry source root checked probes := by simp [observe]

/-- Conditional two-way strict one-step correspondence from the *same*
reachable source representative. This is not a frozen-table run theorem. -/
theorem step_iff (registry : Registry) (root : Occurrence roles) (source : State roles)
 (checked : (Boundary roles).Checked registry)
 (reachable : B4TargetV8.Reachable (Boundary roles) registry root source)
 (probes : Probes roles) (sound : Sound registry source root checked probes)
 (complete : Covers registry source root checked probes) (owners : List Nat) (pool : List Output)
 (target : GeneralRebaseStep258.State (Basis owners pool)) :
 GeneralRebaseStep258.Step (observe registry root source checked probes owners pool)
   (project owners pool source) target ↔
 ∃ after, (Boundary roles).Step registry root source after ∧
   project owners pool after = target ∧ target ≠ project owners pool source := by
 constructor
 · rintro ⟨p,listed,changed,diff⟩
   rw [observe_current] at listed
   obtain ⟨after,step,exact,_⟩ := GeneralRebaseObserverSound267.witness registry root source checked reachable
      probes sound owners pool p listed
   exact ⟨after,step,exact.symm.trans changed.symm,fun eq => diff (congrArg GeneralRebaseStep258.State.remaining eq)⟩
 · rintro ⟨after,step,same,diff⟩
   obtain ⟨p,listed,exact⟩ := GeneralRebaseObserverCoverage267.emits_strict registry root source after
     checked reachable probes complete owners pool step (same.symm ▸ diff)
   refine ⟨p,?_,(exact.trans same).symm,?_⟩
   · rwa [observe_current]
   · exact fun equal => diff (GeneralRebaseStep258.state_ext _ _ equal)

theorem source_basis (registry : Registry) (root : Occurrence roles) (start : State roles)
 (checked : (Boundary roles).Checked registry) (initial : (Boundary roles).Initial registry root start) :
 ∃ owners : List Nat, ∃ pool : List Output, ∀ source,
 B4Target.Steps ((Boundary roles).Step registry root) start source →
 ∀ probes : Probes roles, Sound registry source root checked probes →
 GeneralRebaseClosedObserver259.Closed (observe registry root source checked probes owners pool) := by
 obtain ⟨owners,pool,covers⟩ := GeneralRebaseLiveProjection264.source_covered registry root start initial
 refine ⟨owners,pool,?_⟩
 intro source trace probes sound state p listed fact inProposal
 have reachable : B4TargetV8.Reachable (Boundary roles) registry root source := ⟨start,initial,trace⟩
 unfold observe at listed
 split at listed
 · obtain ⟨after,step,_,subset⟩ := GeneralRebaseObserverSound267.witness registry root source checked reachable
      probes sound owners pool p listed
   exact covers after (.tail trace step) (subset inProposal)
 · cases listed

theorem source_relative_terminal (registry : Registry) (root : Occurrence roles) (source : State roles)
 (checked : (Boundary roles).Checked registry)
 (reachable : B4TargetV8.Reachable (Boundary roles) registry root source)
 (probes : Probes roles) (sound : Sound registry source root checked probes)
 (complete : Covers registry source root checked probes) (owners : List Nat) (pool : List Output) :
 (∀ target, ¬ GeneralRebaseStep258.Step (observe registry root source checked probes owners pool)
   (project owners pool source) target) ↔
 (∀ after, (Boundary roles).Step registry root source after → project owners pool after = project owners pool source) := by
 constructor
 · intro terminal after real
   apply Classical.byContradiction
   intro changed
   exact terminal _ ((step_iff registry root source checked reachable probes sound complete owners pool _).mpr
     ⟨after,real,rfl,changed⟩)
 · intro same target step
   obtain ⟨after,real,ends,diff⟩ :=
     (step_iff registry root source checked reachable probes sound complete owners pool target).mp step
   exact diff (ends.symm.trans (same after real))

end Yulang.GeneralRebaseObserverExact267
