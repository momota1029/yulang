import Yulang.GeneralRebaseFiniteSublists298
import Yulang.GeneralRebaseWeakProgress268

namespace Yulang.GeneralRebaseWeakExit298
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedJournal232 (State)
open GeneralRebaseSourceSurvivor267 (Boundary Encoded)
open GeneralRebaseLocalProgram298 (emit represents reifies)
open GeneralRebaseRevisitedTrace298 (Family reachable_tail)
open GeneralRebaseLiveProjection264 (project)
open GeneralRebaseStep258 (Proposal tryWrite tryWrite_exact write state_ext)
open GeneralRebaseWeakProgress268 (Lull Weak lull_same lull_source)
open GeneralSourceState (Output)

variable {roles : Roles.RoleDecls} {r : Registry} {root : Occurrence roles}
  {checked : (Boundary roles).Checked r}
abbrev View (owners : List Nat) (pool : List Output) :=
  GeneralRebaseStep258.State (GeneralRebaseCompression266.Basis owners pool)

def fromState (codes : Family r root checked) (owners : List Nat) (pool : List Output)
    (start mid : State roles) : List (View owners pool) :=
  (emit (codes mid)).filterMap (tryWrite (project owners pool start))

def exits (codes : Family r root checked) (owners : List Nat) (pool : List Output)
    (start : State roles) (window : List (State roles)) : List (View owners pool) :=
  window.flatMap (fromState codes owners pool start)

theorem listed (codes : Family r root checked) (owners : List Nat) (pool : List Output)
    (s m : State roles) (target : View owners pool) :
    target ∈ fromState codes owners pool s m ↔
    ∃ p ∈ emit (codes m), target = write (project owners pool s) p ∧
      target.remaining ≠ (project owners pool s).remaining := by
  unfold fromState
  rw [List.mem_filterMap]
  exact exists_congr fun p => and_congr_right' (tryWrite_exact ..)

theorem target_sublist (codes : Family r root checked) (owners : List Nat) (pool : List Output)
    (s m : State roles) (target : View owners pool) (member : target ∈ fromState codes owners pool s m) :
    target.remaining.Sublist (project owners pool s).remaining := by
  obtain ⟨p,_,rfl,_⟩ := (listed ..).mp member
  exact List.filter_sublist ..

theorem realizes {codes : Family r root checked} {s m : State roles}
    (seen : B4TargetV8.Reachable (Boundary roles) r root s)
    (owners : List Nat) (pool : List Output)
    (silent : Lull (Encoded r) root owners pool s m)
    (target : View owners pool) (member : target ∈ fromState codes owners pool s m) :
    ∃ after, Weak (Encoded r) root owners pool s after ∧ project owners pool after = target := by
  obtain ⟨p,mem,eq,different⟩ := (listed ..).mp member
  obtain ⟨after,step,actual⟩ := reifies (reachable_tail seen (lull_source silent)) (codes m) owners pool p mem
  have same := lull_same silent
  have atEnd : project owners pool after = target := actual.symm.trans
    ((congrArg (fun q => write q p) same).trans eq.symm)
  refine ⟨after,⟨m,silent,step,?_⟩,atEnd⟩
  intro eq
  exact different (congrArg GeneralRebaseStep258.State.remaining (atEnd.symm.trans (eq.trans same)))

theorem completeness {codes : Family r root checked} {s after : State roles}
    (seen : B4TargetV8.Reachable (Boundary roles) r root s)
    (owners : List Nat) (pool : List Output)
    (weak : Weak (Encoded r) root owners pool s after) :
    ∃ m, Lull (Encoded r) root owners pool s m ∧
      project owners pool after ∈ fromState codes owners pool s m := by
  obtain ⟨m,silent,step,strict⟩ := weak
  obtain ⟨p,mem,real⟩ := represents (reachable_tail seen (lull_source silent)) (codes m) owners pool step strict
  have same := lull_same silent
  refine ⟨m,silent,(listed ..).mpr ⟨p,mem,?_,?_⟩⟩
  · exact (real.symm.trans (congrArg (fun q => write q p) same))
  · intro eq
    exact strict ((state_ext _ _ eq).trans same.symm)

theorem sound_window {codes : Family r root checked} {s : State roles}
    (seen : B4TargetV8.Reachable (Boundary roles) r root s)
    (owners : List Nat) (pool : List Output)
    (window : List (State roles)) (good : ∀ m ∈ window, Lull (Encoded r) root owners pool s m)
    (target : View owners pool) (member : target ∈ exits codes owners pool s window) :
    ∃ after, Weak (Encoded r) root owners pool s after ∧ project owners pool after = target := by
  obtain ⟨m,mem,used⟩ := List.mem_flatMap.mp member
  exact realizes seen owners pool (good m mem) target used

end Yulang.GeneralRebaseWeakExit298
