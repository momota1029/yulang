import Yulang.GeneralRebaseLocalProgram298

namespace Yulang.GeneralRebaseRevisitedTrace298
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedJournal232 (State)
open GeneralRebaseSourceSurvivor267 (Boundary Encoded)
open GeneralRebaseLocalProgram298 (Local emit represents)
open GeneralRebaseLiveProjection264 (project)
open GeneralRebaseStep258 (Proposal write)
open GeneralSourceState (Output)
open B4Target (Steps)

variable {roles : Roles.RoleDecls} {r : Registry} {root : Occurrence roles}
  {checked : (Boundary roles).Checked r}

abbrev Family (r : Registry) (root : Occurrence roles) (checked : (Boundary roles).Checked r) :=
  ∀ s : State roles, Local r s root checked

/-- Retain each raw representative so a silent step can change the inputs
to compilation. The script records only strict projected writes. -/
inductive Trace (codes : Family r root checked) (owners : List Nat) (pool : List Output) :
    State roles → State roles → List Proposal → Prop where
  | nil (s) : Trace codes owners pool s s []
  | silent : Trace codes owners pool s t ps → (Boundary roles).Step r root t u →
      project owners pool t = project owners pool u → Trace codes owners pool s u ps
  | strict : Trace codes owners pool s t ps → (Boundary roles).Step r root t u →
      project owners pool t ≠ project owners pool u →
      p ∈ emit (codes t) → write (project owners pool t) p = project owners pool u →
      Trace codes owners pool s u (ps ++ [p])

theorem raw {codes : Family r root checked} {owners pool s t ps}
    (walk : Trace codes owners pool s t ps) :
    Steps ((Boundary roles).Step r root) s t := by
  induction walk with
  | nil => exact .refl
  | silent _ h _ ih => exact .tail ih h
  | strict _ h _ _ _ ih => exact .tail ih h

theorem reachable_tail {s t : State roles} (start : B4TargetV8.Reachable (Boundary roles) r root s)
    (walk : Steps ((Boundary roles).Step r root) s t) :
    B4TargetV8.Reachable (Boundary roles) r root t := by
  obtain ⟨first,initial,path⟩ := start
  induction walk with
  | refl => exact ⟨first,initial,path⟩
  | tail _ h ih =>
    obtain ⟨origin,formed,steps⟩ := ih
    exact ⟨origin,formed,.tail steps h⟩

theorem compile_path (codes : Family r root checked) (owners : List Nat) (pool : List Output)
    {s t : State roles} (start : B4TargetV8.Reachable (Boundary roles) r root s)
    (walk : Steps ((Boundary roles).Step r root) s t) :
    ∃ ps, Trace codes owners pool s t ps := by
  classical
  induction walk with
  | refl => exact ⟨[],.nil _⟩
  | @tail t u _ step ih =>
    obtain ⟨ps,h⟩ := ih
    by_cases same : project owners pool t = project owners pool u
    · exact ⟨ps,.silent h step same⟩
    · obtain ⟨p,listed,next⟩ := represents (reachable_tail start (raw h)) (codes t) owners pool step (Ne.symm same)
      exact ⟨ps ++ [p],.strict h step same listed next⟩

theorem exact {s t : State roles} (codes : Family r root checked) (owners : List Nat) (pool : List Output)
    (start : B4TargetV8.Reachable (Boundary roles) r root s) :
    (∃ ps, Trace codes owners pool s t ps) ↔ Steps ((Boundary roles).Step r root) s t :=
  ⟨fun ⟨_,trace⟩ => raw trace,compile_path codes owners pool start⟩

theorem replay {codes : Family r root checked} {owners pool s t ps}
    (trace : Trace codes owners pool s t ps) :
    ps.foldl write (project owners pool s) = project owners pool t := by
  induction trace with
  | nil => rfl
  | silent _ _ same ih => exact ih.trans same
  | strict _ _ _ _ wrote ih => rw [List.foldl_append,ih]; exact wrote

theorem strict_budget {codes : Family r root checked} {owners pool s t ps}
    (trace : Trace codes owners pool s t ps) :
    ps.length + (project owners pool t).remaining.length ≤ (project owners pool s).remaining.length := by
  induction trace with
  | nil => simp
  | silent _ _ same ih => simpa only [same] using ih
  | strict _ h different _ _ ih =>
    have drop := GeneralRebaseSourceProjection264.strict_decrease owners pool h (Ne.symm different)
    simp only [List.length_append,List.length_singleton]
    omega

end Yulang.GeneralRebaseRevisitedTrace298
