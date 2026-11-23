import Yulang.GeneralDeclarativeInspect321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65
open GeneralDeclarativeK2Graph321 (Descends Path path_cat)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeGraphRows321 (structural observed)

/-- A cycle certificate for a represented inspected site only needs
to rank structural edges on a path that can return to that site.
Unrelated edges, including edges in disjoint cycles, are not a
precondition for source acceptance or for generation of visits. -/
structure SiteReturnRank (s : GeneralDeclarativeHead320.State) (site : Nat) (rank : Nat → Nat) : Prop where
  fall : ∀ {a b last}, Path (structural s) site a →
    Descends (structural s) a b → Path (structural s) b last →
    GeneralDeclarativeLowerKnown321.Alias s last site → rank b < rank a
  close : ∀ {last}, Path (structural s) site last →
    GeneralDeclarativeLowerKnown321.Alias s last site → rank site ≤ rank last

theorem return_tail_weak {s : GeneralDeclarativeHead320.State} {site a last : Nat}
    {rank : Nat → Nat} (checked : SiteReturnRank s site rank)
    (tail : Path (structural s) a last)
    (arrived : Path (structural s) site a)
    (back : GeneralDeclarativeLowerKnown321.Alias s last site) :
    rank last ≤ rank a := by
  induction tail with
  | refl => exact Nat.le_refl _
  | next step rest ih =>
    have expanded := path_cat arrived (.next step (.refl _))
    exact Nat.le_trans (by apply ih <;> assumption) (Nat.le_of_lt (checked.fall arrived step rest back))

theorem ranked_return_rules_out_cycle {s : GeneralDeclarativeHead320.State} {site : Nat}
    {rank : Nat → Nat} (checked : SiteReturnRank s site rank) :
    ¬AliasCycle s (observed s) site := by
  rintro ⟨first,last,descended,tail,closes⟩
  have began : Path (structural s) site first := .next descended (.refl _)
  have down := checked.fall (.refl _) descended tail closes
  have up := checked.close (path_cat began tail) closes
  exact Nat.not_lt_of_ge (Nat.le_trans up (return_tail_weak checked tail began closes)) down

theorem returning_edge_has_cycle {s : GeneralDeclarativeHead320.State}
    {site a b last : Nat} (arrived : Path (structural s) site a)
    (step : Descends (structural s) a b) (tail : Path (structural s) b last)
    (back : GeneralDeclarativeLowerKnown321.Alias s last site) :
    AliasCycle s (observed s) site := by
  cases arrived with
  | refl => exact ⟨b,last,step,tail,back⟩
  | next first rest => exact ⟨_,last,first,path_cat rest (.next step tail),back⟩

/-- Exact logical expressivity, not a decision algorithm. For an
acyclic site there is no returning structural edge to rank, so
a constant function suffices. This neither strengthens eligibility
nor rules out incomparable/unvisited cycles. -/
theorem local_return_rank_iff_no_cycle (s : GeneralDeclarativeHead320.State) (site : Nat) :
    (∃ rank, SiteReturnRank s site rank) ↔ ¬AliasCycle s (observed s) site := by
  constructor
  · rintro ⟨rank,certified⟩
    exact ranked_return_rules_out_cycle certified
  · intro safe
    refine ⟨fun _ => 0,⟨?_,?_⟩⟩
    · intro a b last arrived edge tail back
      exact (safe (returning_edge_has_cycle arrived edge tail back)).elim
    · intro last arrived back
      exact Nat.le_refl _

/-- Finite implementations can check an explicit forward-closed cut
instead of just asking for an (existential) return rank. This core
result imposes no decision or finiteness hypothesis on the graph. -/
structure SiteEscapeCut (s : GeneralDeclarativeHead320.State) (site : Nat)
    (inside : Nat → Prop) : Prop where
  enters : ∀ {next}, Descends (structural s) site next → inside next
  closed : ∀ {a b}, inside a → Descends (structural s) a b → inside b
  outside : ∀ {n}, inside n → ¬GeneralDeclarativeLowerKnown321.Alias s n site

theorem follows_escape_cut {s : GeneralDeclarativeHead320.State} {site : Nat}
    {inside : Nat → Prop} (cut : SiteEscapeCut s site inside) {a b : Nat}
    (path : Path (structural s) a b) (entered : inside a) : inside b := by
  induction path with
  | refl => exact entered
  | next edge _ ih => exact ih (cut.closed entered edge)

/-- An exact criterion with positive evidence about outgoing edges
and disjointness from the actual root alias class. Cycles inside the
cut are irrelevant if they do not return to the chosen inspected site. -/
theorem local_escape_cut_iff_no_cycle (s : GeneralDeclarativeHead320.State) (site : Nat) :
    (∃ inside,SiteEscapeCut s site inside) ↔ ¬AliasCycle s (observed s) site := by
  constructor
  · rintro ⟨inside,cut⟩ ⟨first,last,begin,rest,closes⟩
    exact cut.outside (follows_escape_cut cut rest (cut.enters begin)) closes
  · intro no
    refine ⟨fun n => ∃ first,Descends (structural s) site first ∧ Path (structural s) first n,⟨?_,?_,?_⟩⟩
    · intro first step
      exact ⟨first,step,.refl _⟩
    · rintro a b ⟨first,begin,already⟩ edge
      exact ⟨first,begin,path_cat already (.next edge (.refl _))⟩
    · rintro last ⟨first,begin,rest⟩ returns
      exact no ⟨first,last,begin,rest,returns⟩

theorem escape_cut_gives_local_return_rank {s : GeneralDeclarativeHead320.State} {site : Nat}
    {inside : Nat → Prop} (cut : SiteEscapeCut s site inside) :
    ∃ rank,SiteReturnRank s site rank :=
  (local_return_rank_iff_no_cycle s site).mpr
    ((local_escape_cut_iff_no_cycle s site).mp ⟨inside,cut⟩)

end Yulang.GeneralDeclarativeI65
