import Yulang.GeneralRebaseCertifiedPathCount266

namespace Yulang.GeneralRebasePathQuiescent266
open GeneralRebaseStep258
open GeneralRebaseCertifiedObserver266 (Edge observe membership)
open GeneralRebaseCertifiedPath266
open GeneralRebaseCertifiedPathCount266 (strict_count exact_terminal_budget)
open GeneralRebaseLiveProjection264 (SourceState project)
open GeneralSourceState (Output)
variable {registry : GeneralDeclarations.Registry} {root : GeneralSourceDictionaries.Occurrence roles}

theorem all_stutter (owners : List Nat) (pool : List Output)
 (path : Path registry root first last) (same : project owners pool first = project owners pool last)
 (edge : Edge registry root) (listed : edge ∈ edges path) :
 project owners pool edge.after = project owners pool edge.before := by
 apply Classical.byContradiction
 intro changed
 have drop := GeneralRebaseSourceProjection264.strict_decrease owners pool edge.actual changed
 obtain ⟨lower,upper⟩ := rank_bounds owners pool path edge listed
 have eq := congrArg (fun state => (state : State _).remaining.length) same
 unfold rank at lower upper
 omega

theorem observer_empty (owners : List Nat) (pool : List Output)
 (path : Path registry root first last) (same : project owners pool first = project owners pool last)
 (state : State (GeneralRebaseCompression266.Basis owners pool)) :
 observe owners pool (edges path) state = [] := by
 apply List.eq_nil_iff_forall_not_mem.mpr
 intro proposal present
 obtain ⟨edge,listed,starts,changed,_⟩ := (membership owners pool (edges path) state proposal).mp present
 exact changed ((all_stutter owners pool path same edge listed).trans starts)

theorem count_zero (owners : List Nat) (pool : List Output)
 (path : Path registry root first last) (same : project owners pool first = project owners pool last) :
 strict_count owners pool path = 0 := by
 have budget := exact_terminal_budget owners pool path
 unfold rank at budget
 rw [same] at budget
 omega

theorem immediate (owners : List Nat) (pool : List Output)
 (path : Path registry root first last) (same : project owners pool first = project owners pool last)
 (state : State (GeneralRebaseCompression266.Basis owners pool)) :
 GeneralRebaseScheduler259.next (observe owners pool (edges path)) state = .ok none := by
 rw [GeneralRebaseScheduler259.next,observer_empty owners pool path same]
 rfl

/-- Existence only: this elimination of an old logical path does not extract
an executable enumerator for unknown source steps. -/
theorem of_round
 (path : Relation.TransGen (fun after before =>
   GeneralNominalVersionedMixedKernel234.Step registry root before after) last first) :
 Nonempty (Path registry root first last) := by
 induction path with
 | single step => exact ⟨Path.cons ⟨_,_,step⟩ (Path.nil _)⟩
 | tail _ head ih =>
   obtain ⟨tail⟩ := ih
   exact ⟨Path.cons ⟨_,_,head⟩ tail⟩

end Yulang.GeneralRebasePathQuiescent266
