import Yulang.GeneralRebasePathRules266

namespace Yulang.GeneralRebasePathFamily266
open GeneralRebaseStep258
open GeneralRebaseBudget258 (Runs)
open GeneralRebaseCertifiedObserver266 (Edge observe step_exact)
open GeneralRebaseCertifiedPath266 (Path edges rank rank_bounds)
open GeneralRebaseCertifiedPathCount266 (strict_count exact_run)
open GeneralRebaseLiveProjection264 (SourceState project)
open GeneralSourceState (Output)
variable {registry : GeneralDeclarations.Registry} {root : GeneralSourceDictionaries.Occurrence roles}

def table (paths : List (Path registry root first last)) : List (Edge registry root) :=
 paths.flatMap edges

theorem from_path (paths : List (Path registry root first last))
 (path : Path registry root first last) (member : path ∈ paths) :
 edges path ⊆ table paths :=
 fun _ listed => List.mem_flatMap.mpr ⟨path,member,listed⟩

theorem edge_path (paths : List (Path registry root first last)) (edge : Edge registry root)
 (member : edge ∈ table paths) :
 ∃ path ∈ paths, edge ∈ edges path :=
 List.mem_flatMap.mp member

theorem suffix (path : Path registry root first last) (edge : Edge registry root)
 (member : edge ∈ edges path) :
 ∃ tail : Path registry root edge.after last, edges tail ⊆ edges path := by
 induction path with
 | nil => simp [edges] at member
 | cons head tail ih =>
   rcases List.mem_cons.mp member with same | later
   · cases same
     exact ⟨tail,fun _ listed => List.mem_cons_of_mem _ listed⟩
   · obtain ⟨subtail,included⟩ := ih later
     exact ⟨subtail,fun _ listed => List.mem_cons_of_mem _ (included listed)⟩

theorem terminal (owners : List Nat) (pool : List Output)
 (paths : List (Path registry root first last)) :
 ∀ after, ¬ Step (observe owners pool (table paths)) (project owners pool last) after := by
 intro after step
 obtain ⟨edge,member,_,ends,_⟩ := (step_exact owners pool (table paths) _ _).mp step
 obtain ⟨path,_,onPath⟩ := edge_path paths edge member
 have lower := (rank_bounds owners pool path edge onPath).1
 have decrease := decreases _ step
 unfold rank at lower
 rw [ends] at lower
 exact Nat.not_lt_of_ge lower decrease


theorem run_end (owners : List Nat) (pool : List Output)
 (paths : List (Path registry root first last))
 {start current : State (GeneralRebaseCompression266.Basis owners pool)}
 (run : Runs (observe owners pool (table paths)) n start current) :
 current = start ∨ ∃ edge ∈ table paths, project owners pool edge.after = current := by
 induction run with
 | nil _ => exact Or.inl rfl
 | next head _ ih =>
   apply Or.inr
   rcases ih with same | edge
   · obtain ⟨e,member,_,ends,_⟩ := (step_exact owners pool (table paths) _ _).mp head
     exact ⟨e,member,ends.trans same.symm⟩
   · exact edge

theorem can_finish (owners : List Nat) (pool : List Output)
 (paths : List (Path registry root first last)) (nonempty : ∃ path, path ∈ paths)
 {current : State (GeneralRebaseCompression266.Basis owners pool)}
 (run : Runs (observe owners pool (table paths)) n (project owners pool first) current) :
 ∃ k, Runs (observe owners pool (table paths)) k current (project owners pool last) := by
 rcases run_end owners pool paths run with same | ⟨edge,member,ends⟩
 · obtain ⟨path,listed⟩ := nonempty
   have witness := exact_run owners pool (table paths) path (from_path paths path listed)
   rw [←same] at witness
   exact ⟨_,witness⟩
 · obtain ⟨path,there,listed⟩ := edge_path paths edge member
   obtain ⟨suf,included⟩ := suffix path edge listed
   have witness := exact_run owners pool (table paths) suf (fun _ h => from_path paths path there (included h))
   rw [ends] at witness
   exact ⟨_,witness⟩

/-- Reaching a common target is invariant under arbitrary edge choice in this
table, though an execution mixing paths need not have a concrete lift. -/
theorem every_terminal (owners : List Nat) (pool : List Output)
 (paths : List (Path registry root first last)) (nonempty : ∃ path, path ∈ paths)
 {current : State (GeneralRebaseCompression266.Basis owners pool)}
 (run : Runs (observe owners pool (table paths)) n (project owners pool first) current)
 (quiet : ∀ after, ¬ Step (observe owners pool (table paths)) current after) :
 current = project owners pool last := by
 obtain ⟨_,suffix⟩ := can_finish owners pool paths nonempty run
 cases suffix with
 | nil _ => rfl
 | next step _ => exact False.elim (quiet _ step)

theorem settles (owners : List Nat) (pool : List Output)
 (paths : List (Path registry root first last)) (nonempty : ∃ path, path ∈ paths) :
 GeneralRebaseSettle259.settle (observe owners pool (table paths)) (project owners pool first) =
 .ok (project owners pool last) := by
 obtain ⟨target,_,success,run,_,quiet⟩ := GeneralRebaseClosedObserver259.completion _
   (GeneralRebaseCertifiedObserver266.closed owners pool (table paths)) (project owners pool first)
 exact success.trans (congrArg Except.ok (every_terminal owners pool paths nonempty run quiet))

end Yulang.GeneralRebasePathFamily266
