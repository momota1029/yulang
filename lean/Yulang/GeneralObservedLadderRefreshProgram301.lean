import Yulang.GeneralObservedLadderRefreshChain301

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralObservedLadderRefreshProgram301
open GeneralObservedLadderSemanticGap301 (equationOnly)
open GeneralObservedLadderSource301 (endpoint)
open GeneralObservedLadderRefresh301 (before after actual endpoint_unknown)
open GeneralObservedLadderRefreshChain301 (outer_atoms advanceFromRefresh step settled list_instance)
open GeneralObservedLadderRoute301 (focus)
open GeneralObservedLadderLedger301 (Phase)
open GeneralObservedLadderEvidence301 (dictionary)
open GeneralObservedLadderJournalCompiler301 (checked_list checked_leaf unrecorded table)
open GeneralNominalVersionedJournal232 (Models)
open GeneralObservedLadderBudget301 (Counted)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalVersionedMixedTerminalStable234 (HeadlessUnknown)
open GeneralNominalExamples (registry displayRoot)
open GeneralDeclarationExamples (roles)
open GeneralNominalCommonBridge (Assignment)
open GeneralGeneratedDictionaryNodes299 (Nodes)
open GeneralGeneratedDictionaryRun299 (run)
open CommonRoleOutermostResolver (Dictionary)

theorem old_source_support (n a : Nat) (seen : a ∈ GeneralNominalState.sources (equationOnly n).state) : a ≤ n+1 := by
  change a ∈ List.ofFn (Fin.val : Fin (n+2) → Nat) ++ List.ofFn (Fin.val : Fin (n+2) → Nat) ++ [] ++
    (GeneralObservedLadderRefresh301.atomTail n).flatMap GeneralNominalState.atomSources at seen
  rw [outer_atoms] at seen
  simp only [List.append_nil,List.mem_append] at seen
  rcases seen with (left|right)|atom
  · obtain ⟨slot,eq⟩ := List.mem_ofFn.mp left
    exact eq ▸ Nat.le_of_lt_succ slot.isLt
  · obtain ⟨slot,eq⟩ := List.mem_ofFn.mp right
    exact eq ▸ Nat.le_of_lt_succ slot.isLt
  · have atEnd : a = n+1 := by simpa [GeneralNominalState.atomSources,GeneralNominalState.typeSources] using atom
    exact Nat.le_of_eq atEnd

theorem earlier_known (n a : Nat) (low : a ≤ n) : GeneralNominalState.Known (equationOnly n).state a := by
  let pos : Fin (n+2) := ⟨a,by omega⟩
  refine ⟨pos,rfl,.inr ⟨GeneralNominalOutputGrowthModels.descriptor n pos low,?_⟩⟩
  exact dite_eq_left low

theorem strict_focus (n a : Nat) (seen : a ∈ GeneralNominalState.sources (equationOnly n).state)
    (unknown : ¬ GeneralNominalState.Known (equationOnly n).state a) : a = n+1 := by
  have top := old_source_support n a seen
  by_cases low : a ≤ n
  · exact False.elim (unknown (earlier_known n a low))
  · omega

theorem not_headless (n : Nat) : ¬ HeadlessUnknown (before n) := by
  rintro ⟨m,valid,headless⟩
  have scalar := ((GeneralNominalPeelingSources.source_models n m).mp valid.1.1).2
  exact headless (n+1) (GeneralNominalAllocationSupport.slot_source (equationOnly n).state (endpoint n))
    (endpoint_unknown n) (.scalar .int) scalar

theorem counted (n k : Nat) (cap : k ≤ n+1) :
    Counted (k+1) (before n) (advanceFromRefresh n k cap).state := by
  induction k with
  | zero => exact .tail (.refl _) (actual n)
  | succ k ih => exact .tail (ih (by omega)) (step n k (by omega))

theorem no_edges_at_actual_refresh (n : Nat) :
    (after n).core.erased.current.edges = (before n).core.erased.current.edges := rfl

theorem terminal_table (p : Phase n (n+1)) :
    table p.state = GeneralObservedLadderObserver301.table n := by
  funext i
  unfold table
  by_cases hi : i ≤ n
  · rw [checked_list p i (by omega) hi,ite_eq_left (by omega),GeneralObservedLadderObserver301.branch n i hi]
  by_cases atEnd : i = n+1
  · subst i
    rw [checked_leaf,GeneralObservedLadderObserver301.leaf]
  rw [unrecorded p i (by omega),GeneralObservedLadderObserver301.out_of_range n i (by omega)]

theorem computes (n : Nat) :
    run (table (settled n).state) (n+2) 0 = some (dictionary (n+1)) := by
  rw [terminal_table]
  exact GeneralObservedLadderReadback301.computed n

theorem nodes (n : Nat) : Nodes (boundary roles) registry (settled n).state
    (GeneralObservedLadderObserver301.table n) (focus n) := by
  intro i row hit model valid ds kids
  rcases GeneralObservedLadderObserver301.entries n i row hit with ⟨hi,rfl⟩|⟨rfl,rfl⟩
  · exact GeneralNominalVersionedEvidence231.evidence_node (list_instance n i hi model valid) kids
  · exact GeneralNominalVersionedEvidence231.evidence_node
      (GeneralObservedLadderLeaf301.terminal_instance (settled n) model valid) kids

theorem compiler_sound (n i fuel : Nat) (d : Dictionary)
    (read : run (table (settled n).state) fuel i = some d)
    (m : Assignment) (valid : Models (settled n).state m) :
    (boundary roles).Evidence registry (settled n).state m (focus n i) d := by
  rw [terminal_table] at read
  exact GeneralGeneratedDictionaryNodes299.same_model (b:=boundary roles) (r:=registry) (s:=(settled n).state)
    _ _ (nodes n) m valid fuel i d read

/-- Existence of a particular witnessed refresh-first path, not exclusion of
other raw schedules from the equation-only initial state. -/
theorem actual_refresh_then_compile (n : Nat) :
    Counted (n+2) (before n) (settled n).state ∧
    run (table (settled n).state) (n+2) 0 = some (dictionary (n+1)) ∧
    ∀ m, Models (settled n).state m →
      (boundary roles).Evidence registry (settled n).state m displayRoot (dictionary (n+1)) := by
  refine ⟨counted n (n+1) (Nat.le_refl _),computes n,?_⟩
  intro m valid
  exact compiler_sound n 0 (n+2) _ (computes n) m valid

end Yulang.GeneralObservedLadderRefreshProgram301
