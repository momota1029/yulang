import Yulang.GeneralRebaseSilentFactor298
import Yulang.GeneralRebaseRefreshPayload298

namespace Yulang.GeneralRebaseExplicitWindow298
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedJournal232 (State)
open GeneralRebaseSourceSurvivor267 (Boundary Encoded)
open GeneralRebaseLocalProgram298 (Local emit)
open GeneralRebaseRevisitedTrace298 (Family)
open GeneralRebaseWeakProgress268 (Lull Weak)
open GeneralRebaseWeakExit298 (View)
open GeneralRebaseLiveProjection264 (project)
open GeneralSourceState (Output)
open GeneralRebaseStep258 (tryWrite)

structure Entry (r : Registry) (root : Occurrence roles) (checked : (Boundary roles).Checked r) where
  state : State roles
  code : Local r state root checked

def scan {r : Registry} {root : Occurrence roles} {checked : (Boundary roles).Checked r}
    (owners : List Nat) (pool : List Output) (start : State roles) (window : List (Entry r root checked)) :
    List (View owners pool) :=
  window.flatMap fun entry => (emit entry.code).filterMap (tryWrite (project owners pool start))

def materialized {r : Registry} {root : Occurrence roles} {checked : (Boundary roles).Checked r}
    (codes : Family r root checked) (window : List (State roles)) : List (Entry r root checked) :=
  window.map fun s => ⟨s,codes s⟩

theorem agrees {r : Registry} {root : Occurrence roles} {checked : (Boundary roles).Checked r}
    (codes : Family r root checked) (owners : List Nat) (pool : List Output)
    (start : State roles) (window : List (State roles)) :
    scan owners pool start (materialized codes window) = GeneralRebaseWeakExit298.exits codes owners pool start window := by
  induction window with
  | nil => rfl
  | cons head tail ih =>
    simp only [scan,materialized,List.map_cons,List.flatMap_cons,GeneralRebaseWeakExit298.exits]
    congr 1

theorem safe_scan {r : Registry} {root : Occurrence roles} {checked : (Boundary roles).Checked r}
    {s : State roles} (reached : B4TargetV8.Reachable (Boundary roles) r root s)
    (owners : List Nat) (pool : List Output) (window : List (Entry r root checked))
    (good : ∀ e ∈ window, Lull (Encoded r) root owners pool s e.state)
    (t : View owners pool) (found : t ∈ scan owners pool s window) :
    ∃ u, Weak (Encoded r) root owners pool s u ∧ project owners pool u = t := by
  obtain ⟨e,listed,some⟩ := List.mem_flatMap.mp found
  classical
  let codes : Family r root checked := fun a =>
    if eq : e.state = a then eq ▸ e.code else GeneralRebaseLocalProgram298.classicalLocal r a root checked
  have useCode : codes e.state = e.code := by simp only [codes,dite_eq_left rfl]
  apply GeneralRebaseWeakExit298.realizes (codes := codes) reached owners pool (good e listed) t
  unfold GeneralRebaseWeakExit298.fromState
  rwa [useCode]

namespace Actual
open GeneralDictionaryOutputDepth252 (sourceRegistry root initial roles reachable)
open GeneralRebaseOutputDepthSuccessor271 (owner output)
open GeneralRebaseSignedDepth297 (checked)
open GeneralRebasePreInstallReplay297 (after actual_before_install)
open GeneralRebaseRefreshCode298 (rawCode)
open GeneralRebaseRefreshInstall298 (before_projection)

def window : List (Entry sourceRegistry root checked) := [⟨after,rawCode⟩]

def evaluated := scan [owner] [output] initial window

theorem only_one : evaluated.length = 1 := by decide +kernel

theorem sole_target : evaluated.map (·.remaining) = [[]] := by decide +kernel

theorem concrete_real_target :
    ∃ u, Weak (Encoded sourceRegistry) root [owner] [output] initial u ∧
      (project [owner] [output] u).remaining = [] := by
  have existsRow : ∃ t, t ∈ evaluated ∧ t.remaining = [] := List.mem_map.mp (sole_target.symm ▸ List.mem_cons_self ..)
  obtain ⟨t,member,goal⟩ := existsRow
  have good : ∀ e ∈ window, Lull (Encoded sourceRegistry) root [owner] [output] initial e.state := by
    intro e listed
    cases List.mem_singleton.mp listed
    exact .tail .refl ⟨actual_before_install,before_projection.symm⟩
  obtain ⟨u,w,actual⟩ := safe_scan reachable [owner] [output] window good t member
  exact ⟨u,w,(congrArg GeneralRebaseStep258.State.remaining actual).trans goal⟩

end Actual
end Yulang.GeneralRebaseExplicitWindow298
