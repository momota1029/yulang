import Yulang.GeneralRebasePathQuiescent266

namespace Yulang.GeneralRebasePathCut266
open GeneralRebaseStep258
open GeneralRebaseCertifiedObserver266 (Edge observe chosen chosen_exact)
open GeneralRebaseCertifiedPath266
open GeneralRebaseCertifiedPathCount266 (strict_count)
open GeneralRebaseLiveProjection264 (SourceState project)
open GeneralSourceState (Output)
variable {registry : GeneralDeclarations.Registry} {root : GeneralSourceDictionaries.Occurrence roles}

theorem count_cons (owners : List Nat) (pool : List Output) (edge : Edge registry root)
 (path : Path registry root edge.after last) :
 strict_count owners pool (.cons edge path) =
  strict_count owners pool path +
    (if chosen owners pool (project owners pool edge.before) edge then 1 else 0) := by
 cases h : chosen owners pool (project owners pool edge.before) edge <;>
   simp [strict_count,edges,h]

/-- A cut after exactly a prescribed number of strict projected transitions
of a supplied certified spine. Edges (including stutters) are not fabricated
or reordered. At zero the earliest cut is the original source vertex. -/
theorem cut (owners : List Nat) (pool : List Output) (path : Path registry root first last)
 (n : Nat) (bound : n ≤ strict_count owners pool path) :
 ∃ mid, ∃ pre : Path registry root first mid, ∃ suf : Path registry root mid last,
 edges pre ++ edges suf = edges path ∧ strict_count owners pool pre = n := by
 induction path generalizing n with
 | nil state =>
   have z : n = 0 := Nat.eq_zero_of_le_zero bound
   exact ⟨state,.nil _,.nil _,rfl,z.symm⟩
 | cons edge tail ih =>
   cases n with
   | zero => exact ⟨edge.before,.nil _,.cons edge tail,rfl,rfl⟩
   | succ n =>
     rw [count_cons] at bound
     cases active : chosen owners pool (project owners pool edge.before) edge with
     | false =>
       simp only [active, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at bound
       obtain ⟨mid,pre,suf,ordered,count⟩ := ih (n+1) bound
       refine ⟨mid,.cons edge pre,suf,?_,?_⟩
       · simpa only [edges,List.cons_append] using congrArg (List.cons edge) ordered
       · rw [count_cons,active,count]
         rfl
     | true =>
       simp only [active, ↓reduceIte] at bound
       obtain ⟨mid,pre,suf,ordered,count⟩ := ih n (Nat.le_of_succ_le_succ bound)
       refine ⟨mid,.cons edge pre,suf,?_,?_⟩
       · simpa only [edges,List.cons_append] using congrArg (List.cons edge) ordered
       · rw [count_cons,active,count]
         rfl

theorem prefix_edges {pre : Path registry root first mid} {suf : Path registry root mid last}
 {path : Path registry root first last} (ordered : edges pre ++ edges suf = edges path) :
 edges pre ⊆ edges path := by
 intro edge listed
 rw [←ordered]
 exact List.mem_append_left _ listed

theorem suffix_edges {pre : Path registry root first mid} {suf : Path registry root mid last}
 {path : Path registry root first last} (ordered : edges pre ++ edges suf = edges path) :
 edges suf ⊆ edges path := by
 intro edge listed
 rw [←ordered]
 exact List.mem_append_right _ listed

end Yulang.GeneralRebasePathCut266
