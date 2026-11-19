import Yulang.GeneralRebaseCertifiedObserver266
import Yulang.GeneralRebaseRoundProjection265

namespace Yulang.GeneralRebaseCertifiedPath266
open GeneralRebaseStep258
open GeneralRebaseBudget258 (Runs)
open GeneralRebaseCertifiedObserver266 (Edge observe step_exact)
open GeneralRebaseLiveProjection264 (SourceState project)
open GeneralSourceState (Output)
variable {registry : GeneralDeclarations.Registry} {root : GeneralSourceDictionaries.Occurrence roles}

/-- A finite composable source path; each edge carries its old-kernel certificate. -/
inductive Path (registry : GeneralDeclarations.Registry)
 (root : GeneralSourceDictionaries.Occurrence roles) : SourceState roles → SourceState roles → Type where
 | nil (state) : Path registry root state state
 | cons (edge : Edge registry root) (tail : Path registry root edge.after last) :
   Path registry root edge.before last

def edges : Path registry root first last → List (Edge registry root)
 | .nil _ => []
 | .cons edge tail => edge :: edges tail

def rank (owners : List Nat) (pool : List Output) (state : SourceState roles) : Nat :=
 (project owners pool state).remaining.length

theorem edge_rank (owners : List Nat) (pool : List Output) (edge : Edge registry root) :
 rank owners pool edge.after ≤ rank owners pool edge.before := by
 rcases GeneralRebaseRoundProjection265.step_or_decrease owners pool edge.actual with same | drop
 · simp only [rank, same, Nat.le_refl]
 · exact Nat.le_of_lt drop

theorem rank_path (owners : List Nat) (pool : List Output)
 (path : Path registry root first last) :
 rank owners pool last ≤ rank owners pool first := by
 induction path with
 | nil => exact Nat.le_refl _
 | cons edge _ ih => exact Nat.le_trans ih (edge_rank owners pool edge)

theorem rank_bounds (owners : List Nat) (pool : List Output)
 (path : Path registry root first last) (edge : Edge registry root)
 (member : edge ∈ edges path) :
 rank owners pool last ≤ rank owners pool edge.after ∧
 rank owners pool edge.before ≤ rank owners pool first := by
 induction path with
 | nil state => simp [edges] at member
 | cons head tail ih =>
   rcases List.mem_cons.mp member with same | later
   · cases same
     exact ⟨rank_path owners pool tail, Nat.le_refl _⟩
   · exact ⟨(ih later).1, Nat.le_trans (ih later).2 (edge_rank owners pool head)⟩

theorem projected (owners : List Nat) (pool : List Output) (table : List (Edge registry root))
 (path : Path registry root first last) (included : edges path ⊆ table) :
 ∃ count, count ≤ (edges path).length ∧
 Runs (observe owners pool table) count (project owners pool first) (project owners pool last) := by
 induction path with
 | nil state => exact ⟨0, Nat.zero_le _, .nil _⟩
 | cons edge tail ih =>
   obtain ⟨n, bound, run⟩ := ih (fun _ member => included (List.mem_cons_of_mem _ member))
   by_cases same : project owners pool edge.after = project owners pool edge.before
   · exact ⟨n, Nat.le_trans bound (Nat.le_succ _), same ▸ run⟩
   · have step := (step_exact owners pool table _ _).mpr
       ⟨edge,included (List.mem_cons_self),rfl,rfl,same⟩
     exact ⟨n+1, Nat.succ_le_succ bound, .next step run⟩

theorem terminal (owners : List Nat) (pool : List Output) (path : Path registry root first last) :
 ∀ after, ¬ Step (observe owners pool (edges path)) (project owners pool last) after := by
 intro after step
 obtain ⟨edge,member,starts,ends,different⟩ := (step_exact owners pool (edges path) _ _).mp step
 have lower := (rank_bounds owners pool path edge member).1
 have decrease := decreases _ step
 unfold rank at lower
 rw [ends] at lower
 exact Nat.not_lt_of_ge lower decrease

end Yulang.GeneralRebaseCertifiedPath266
