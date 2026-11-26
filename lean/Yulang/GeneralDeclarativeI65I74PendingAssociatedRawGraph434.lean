import Yulang.GeneralDeclarativeI65I74PendingAssociatedParentEquality434

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.PendingAssociated434
open GeneralDeclarativeI65
open GeneralDeclarativeBounds319 (Bound)
open GeneralDeclarativeLowerKnown321 (Alias)
open GeneralDeclarativeK2Graph321 (Descends Path)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeGraphRows321 (observed structural)
open GeneralDeclarativeHead320 (Equation)
open Checker408 (Problem Result)

private theorem exact_episode_bounds_only_refl434 {s q} (o : LiteralEpisode434 s q)
    {a b} (h : Bound s.core.current.ordinary.normal a b) : a = b := by
  induction h with
  | interval mem => rw [o.noIntervals] at mem; cases mem
  | constraint mem => rw [o.noAtoms] at mem; cases mem
  | refl => rfl
  | trans _ _ first last => exact first.trans last

theorem exact_episode_alias_only_refl434 {s q} (o : LiteralEpisode434 s q)
    {a b} (h : GeneralDeclarativeLowerKnown321.Alias s.core.current.ordinary a b) : a = b := by
  induction h with
  | bounds lo _ => exact exact_episode_bounds_only_refl434 o lo
  | forward mem =>
    simp [o.exactRows,outerRow434,retainedOutput434,untouchedOutput434] at mem
    exact mem.1.trans mem.2.symm
  | backward mem =>
    simp [o.exactRows,outerRow434,retainedOutput434,untouchedOutput434] at mem
    exact mem.2.trans mem.1.symm
  | trans _ _ first last => exact first.trans last

/-- The ordinary graph includes the speculative output edge exactly as
written. Its only two structural edges are seed → A and A → B; the
ordinary storage equation B = B contributes no structural edge. -/
theorem exact_episode_unfiltered_edges434 {s q} (o : LiteralEpisode434 s q)
    {a b} (edge : Descends (structural s.core.current.ordinary) a b) :
    (a = o.seed.slot ∧ b = o.a) ∨ (a = o.a ∧ b = o.b) := by
  obtain ⟨head,atRoot,child⟩ := edge
  obtain ⟨author,alias,observedHere⟩ := atRoot
  obtain ⟨expr,mem,decoded⟩ := observedHere
  cases exact_episode_alias_only_refl434 o alias
  rw [o.exactRows] at mem
  simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with outer|retained|reflRow
  · have atSlot := congrArg Equation.left outer
    have atExpr := congrArg Equation.right outer
    change a = o.seed.slot at atSlot
    change expr = .nominal o.key [.variable o.a] at atExpr
    rw [atExpr] at decoded
    change some (.nominal o.key [o.a]) = some head at decoded
    cases decoded
    exact .inl ⟨atSlot,by simpa [GeneralDeclarativeK2Graph321.Shape.children] using child⟩
  · have atSlot := congrArg Equation.left retained
    have atExpr := congrArg Equation.right retained
    change a = o.a at atSlot
    change expr = .nominal o.key [.variable o.b] at atExpr
    rw [atExpr] at decoded
    change some (.nominal o.key [o.b]) = some head at decoded
    cases decoded
    exact .inr ⟨atSlot,by simpa [GeneralDeclarativeK2Graph321.Shape.children] using child⟩
  · have atExpr := congrArg Equation.right reflRow
    change expr = .variable o.b at atExpr
    rw [atExpr] at decoded
    cases decoded

/-- Conversely both of those edges are present in the unfiltered State.
In particular the pending output is observable for K2 even though
that same row is not a legal source head in the supported view. -/
theorem exact_episode_unfiltered_edges_iff434 {s q} (o : LiteralEpisode434 s q)
    {a b} :
    Descends (structural s.core.current.ordinary) a b ↔
      (a = o.seed.slot ∧ b = o.a) ∨ (a = o.a ∧ b = o.b) := by
  refine ⟨exact_episode_unfiltered_edges434 o,?_⟩
  rintro (⟨rfl,rfl⟩|⟨rfl,rfl⟩)
  · refine ⟨.nominal o.key [o.a],GeneralDeclarativeGraphRows321.literal_head (exp := .nominal o.key [.variable o.a]) ?_ rfl,
      List.mem_cons_self⟩
    change outerRow434 o.key o.seed.slot o.a ∈ s.core.current.ordinary.equations
    rw [o.exactRows]
    exact List.mem_cons_self
  · refine ⟨.nominal o.key [o.b],GeneralDeclarativeGraphRows321.literal_head (exp := .nominal o.key [.variable o.b]) ?_ rfl,
      List.mem_cons_self⟩
    change retainedOutput434 o.key o.a o.b ∈ s.core.current.ordinary.equations
    rw [o.exactRows]
    exact List.mem_cons_of_mem _ List.mem_cons_self

private def exactEpisodeRank434 {s q} (o : LiteralEpisode434 s q) (n : Nat) : Nat :=
  if n = o.seed.slot then 2 else if n = o.a then 1 else 0

private theorem exact_episode_edge_decreases434 {s q} (o : LiteralEpisode434 s q)
    {a b} (edge : Descends (structural s.core.current.ordinary) a b) :
    exactEpisodeRank434 o b < exactEpisodeRank434 o a := by
  rcases exact_episode_unfiltered_edges434 o edge with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · simp [exactEpisodeRank434,o.sourceNeA.symm]
  · simp [exactEpisodeRank434,o.sourceNeA.symm,o.sourceNeB.symm,o.aNeB.symm]

private theorem exact_episode_path_does_not_increase434 {s q} (o : LiteralEpisode434 s q)
    {a b} (path : Path (structural s.core.current.ordinary) a b) :
    exactEpisodeRank434 o b ≤ exactEpisodeRank434 o a := by
  induction path with
  | refl => exact Nat.le_refl _
  | next edge _ rest =>
      exact Nat.le_trans rest (Nat.le_of_lt (exact_episode_edge_decreases434 o edge))

/-- No given escape ranks occur in this mathematical consequence.
The actual executable witness still reads the full raw graph via the
unchanged K2 logic, including outside this exact graph scope. -/
theorem exact_literal_episode_has_no_raw_K2_at_any_site434 {s q} (o : LiteralEpisode434 s q)
    (site : Nat) : ¬ AliasCycle s.core.current.ordinary (observed s.core.current.ordinary) site := by
  rintro ⟨first,last,edge,path,back⟩
  have lt := Nat.lt_of_le_of_lt (exact_episode_path_does_not_increase434 o path)
    (exact_episode_edge_decreases434 o edge)
  rw [exact_episode_alias_only_refl434 o back] at lt
  exact Nat.lt_irrefl _ lt

theorem exact_accepted_episode_contains_no_unfiltered_K2_434 {p : Problem} {r : Result} {w : Wire}
    (yes : check p r (.pendingAssociated w) = true) :
    ∀ site, ¬ AliasCycle p.state.core.current.ordinary (observed p.state.core.current.ordinary) site := by
  obtain ⟨o,_,_⟩ := checked_pending_reads_actual_original_episode434 yes
  exact exact_literal_episode_has_no_raw_K2_at_any_site434 o.original.episode

end Yulang.GeneralDeclarativeI65.I72.PendingAssociated434
