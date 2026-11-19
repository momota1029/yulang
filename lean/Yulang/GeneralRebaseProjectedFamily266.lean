import Yulang.GeneralRebasePathFamilyRules266

namespace Yulang.GeneralRebaseProjectedFamily266
open GeneralRebaseStep258
open GeneralRebaseBudget258 (Runs)
open GeneralRebaseCertifiedObserver266 (Edge observe step_exact)
open GeneralRebaseCertifiedPath266 (Path edges rank rank_bounds)
open GeneralRebaseCertifiedPathCount266 (exact_run)
open GeneralRebaseLiveProjection264 (SourceState project)
open GeneralSourceState (Output)
variable {registry : GeneralDeclarations.Registry} {root : GeneralSourceDictionaries.Occurrence roles}

abbrev Route (registry : GeneralDeclarations.Registry)
 (root : GeneralSourceDictionaries.Occurrence roles) (first : SourceState roles) :=
 Σ last : SourceState roles, Path registry root first last

def table (routes : List (Route registry root first)) : List (Edge registry root) :=
 routes.flatMap fun route => edges route.2

theorem included (routes : List (Route registry root first)) (route : Route registry root first)
 (listed : route ∈ routes) : edges route.2 ⊆ table routes :=
 fun _ member => List.mem_flatMap.mpr ⟨route,listed,member⟩

theorem provenance (routes : List (Route registry root first)) (edge : Edge registry root)
 (member : edge ∈ table routes) :
 ∃ route ∈ routes, edge ∈ edges route.2 := List.mem_flatMap.mp member

def CommonTarget (owners : List Nat) (pool : List Output) (routes : List (Route registry root first))
 (target : State (GeneralRebaseCompression266.Basis owners pool)) : Prop :=
 ∀ route ∈ routes, project owners pool route.1 = target

theorem terminal (owners : List Nat) (pool : List Output) (routes : List (Route registry root first))
 {target : State (GeneralRebaseCompression266.Basis owners pool)}
 (common : CommonTarget owners pool routes target) :
 ∀ after, ¬ Step (observe owners pool (table routes)) target after := by
 intro after step
 obtain ⟨edge,member,_,ends,_⟩ := (step_exact owners pool (table routes) _ _).mp step
 obtain ⟨route,listed,onRoute⟩ := provenance routes edge member
 have lower := (rank_bounds owners pool route.2 edge onRoute).1
 unfold rank at lower
 rw [common route listed,ends] at lower
 exact Nat.not_lt_of_ge lower (decreases _ step)

theorem run_end (owners : List Nat) (pool : List Output) (routes : List (Route registry root first))
 {start current : State (GeneralRebaseCompression266.Basis owners pool)}
 (run : Runs (observe owners pool (table routes)) n start current) :
 current = start ∨ ∃ edge ∈ table routes, project owners pool edge.after = current := by
 induction run with
 | nil _ => exact Or.inl rfl
 | next step _ ih =>
   apply Or.inr
   rcases ih with same | witnessed
   · obtain ⟨edge,listed,_,ends,_⟩ := (step_exact owners pool (table routes) _ _).mp step
     exact ⟨edge,listed,ends.trans same.symm⟩
   · exact witnessed

theorem can_finish (owners : List Nat) (pool : List Output) (routes : List (Route registry root first))
 (nonempty : ∃ route, route ∈ routes) {target current : State (GeneralRebaseCompression266.Basis owners pool)}
 (common : CommonTarget owners pool routes target)
 (run : Runs (observe owners pool (table routes)) n (project owners pool first) current) :
 ∃ k, Runs (observe owners pool (table routes)) k current target := by
 rcases run_end owners pool routes run with same | ⟨edge,listed,ends⟩
 · obtain ⟨route,member⟩ := nonempty
   have witness := exact_run owners pool (table routes) route.2 (included routes route member)
   rw [←same,common route member] at witness
   exact ⟨_,witness⟩
 · obtain ⟨route,member,onRoute⟩ := provenance routes edge listed
   obtain ⟨suf,sub⟩ := GeneralRebasePathFamily266.suffix route.2 edge onRoute
   have witness := exact_run owners pool (table routes) suf (fun _ h => included routes route member (sub h))
   rw [ends,common route member] at witness
   exact ⟨_,witness⟩

theorem every_terminal (owners : List Nat) (pool : List Output) (routes : List (Route registry root first))
 (nonempty : ∃ route, route ∈ routes) {target current : State (GeneralRebaseCompression266.Basis owners pool)}
 (common : CommonTarget owners pool routes target)
 (run : Runs (observe owners pool (table routes)) n (project owners pool first) current)
 (quiet : ∀ after, ¬ Step (observe owners pool (table routes)) current after) : current = target := by
 obtain ⟨_,ending⟩ := can_finish owners pool routes nonempty common run
 cases ending with
 | nil _ => rfl
 | next step _ => exact False.elim (quiet _ step)

theorem settles (owners : List Nat) (pool : List Output) (routes : List (Route registry root first))
 (nonempty : ∃ route, route ∈ routes) {target : State (GeneralRebaseCompression266.Basis owners pool)}
 (common : CommonTarget owners pool routes target) :
 GeneralRebaseSettle259.settle (observe owners pool (table routes)) (project owners pool first) =
 .ok target := by
 obtain ⟨_,_,success,run,_,quiet⟩ := GeneralRebaseClosedObserver259.completion _
   (GeneralRebaseCertifiedObserver266.closed owners pool (table routes)) (project owners pool first)
 exact success.trans (congrArg Except.ok (every_terminal owners pool routes nonempty common run quiet))

end Yulang.GeneralRebaseProjectedFamily266
