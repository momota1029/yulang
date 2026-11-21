import Yulang.GeneralSharedNamedPremerge310

set_option backward.isDefEq.respectTransparency false
/-! A concrete diagnostic readback that retains the actual sibling merge edge.
Scope is the two proved checkpoints; no arbitrary state-to-frontier compiler
is asserted. -/
namespace Yulang.GeneralSharedNamedDiagnostic310
open GeneralSharedNamedSource310 (root registry)
open GeneralSharedNamedPlan310 (loSite hiSite)
open GeneralSharedNamedInstall310 (after)
open GeneralSharedNamedMerge310 (merged aliases)
open GeneralSharedNamedSelection310 (actual_pick)
open GeneralSharedNamedCompiler310 (decode row read)
open GeneralSharedNamedPremerge310 (before)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedMixedSourceBoundary234 (Local)
open GeneralDeclarationExamples (roles)
open GeneralPartialDiagnosticRead310 (Read Faithful check)
open CommonRoleOutermostResolver (Tree Resolves)

def afterTable : Read := fun i =>
  (read i).map fun entry => .selected entry.key entry.children

def sawMerge (s : State roles) : Bool :=
  decide ((loSite.occurrence.identity,hiSite.occurrence.identity) ∈ s.core.erased.current.aliases)

def atState (s : State roles) : Read :=
  if sawMerge s then afterTable else GeneralSharedNamedPremerge310.read

theorem event_before : sawMerge after = false := rfl

theorem event_after : sawMerge merged = true := by
  unfold sawMerge
  rw [aliases]
  simp

theorem chosen_before : atState after = GeneralSharedNamedPremerge310.read := by simp [atState,event_before]
theorem chosen_after : atState merged = afterTable := by simp [atState,event_after]

theorem after_faithful : Faithful afterTable decode (Local registry merged) := by
  intro i r hit
  unfold afterTable at hit
  cases readEq : read i with
  | none => simp [readEq] at hit
  | some e =>
    have eq : .selected e.key e.children = r := Option.some.inj (by simpa only [readEq,Option.map_some] using hit)
    subst r
    exact GeneralSharedNamedCompiler310.faithful i e readEq

theorem real_checkpoints (s : State roles) (actual : s = after ∨ s = merged) :
    Faithful (atState s) decode (Local registry s) := by
  rcases actual with rfl|rfl
  · rw [chosen_before]
    exact GeneralSharedNamedPremerge310.faithful
  · rw [chosen_after]
    exact after_faithful

theorem table_root : afterTable 0 = some (.selected 1 [1,2]) := by
  change some (CommonRoleOutermostResolver.Frontier.selected (row .parent).key (row .parent).children) = _
  rw [GeneralSharedNamedCompiler310.row_exact]
  rfl

theorem table_low : afterTable 1 = some (.selected 2 []) := by
  change some (CommonRoleOutermostResolver.Frontier.selected (row .low).key (row .low).children) = _
  rw [GeneralSharedNamedCompiler310.row_exact]
  rfl

theorem table_high : afterTable 2 = some (.selected 2 []) := by
  change some (CommonRoleOutermostResolver.Frontier.selected (row .high).key (row .high).children) = _
  rw [GeneralSharedNamedCompiler310.row_exact]
  rfl

def complete : Tree := .selected 1 [.selected 2 [],.selected 2 []]

theorem distinguishes :
    check (atState after) 2 0 before = true ∧ check (atState after) 2 0 complete = false ∧
    check (atState merged) 2 0 before = false ∧ check (atState merged) 2 0 complete = true := by
  rw [chosen_before,chosen_after]
  refine ⟨rfl,rfl,?_,?_⟩
  · simp [before,check,table_root,table_low,GeneralPartialDiagnosticRead310.check.rows]
  · simp [complete,check,table_root,table_low,table_high,GeneralPartialDiagnosticRead310.check.rows]

theorem verified_after : Resolves (Local registry merged) root complete :=
  GeneralPartialDiagnosticRead310.sound _ decode (Local registry merged)
    (real_checkpoints _ (.inr rfl)) 2 0 complete distinguishes.2.2.2

end Yulang.GeneralSharedNamedDiagnostic310
