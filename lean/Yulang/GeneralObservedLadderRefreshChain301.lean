import Yulang.GeneralObservedLadderRefresh301

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralObservedLadderRefreshChain301
open GeneralObservedLadderInitial301 (initial)
open GeneralObservedLadderRefresh301 (after before refined atomTail actual refresh_models)
open GeneralObservedLadderSemanticGap301 (same_models)
open GeneralObservedLadderRoute301
open GeneralObservedLadderLedger301
open GeneralObservedLadderAdvance301 (advance)
open GeneralObservedLadderEnabled301 (effect)
open GeneralObservedLadderEvidence301 (replay replay_prepared replay_held replay_children dictionary)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalVersionedJournal232 (Models State)
open GeneralNominalExamples (registry displayRoot)
open GeneralDeclarationExamples (roles)
open GeneralNominalIdentities (source)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedInstallation231 (allocated)
open GeneralNominalVersionedEvidence231 (Frame Instance)
open GeneralObservedLadderPlan301 (compiled)
open B4Target (Steps)

theorem before_models (n : Nat) (m : Assignment) :
    Models (before n) m ↔ Models (initial n) m := by
  rw [GeneralNominalVersionedJournal232.initial_models,GeneralNominalVersionedJournal232.initial_models,
      same_models n m]
  rfl

theorem outer_atoms (n : Nat) :
    atomTail n = [.tyLe (.var (n+1)) (.base .int),.tyLe (.base .int) (.var (n+1))] := rfl

def ready (n : Nat) : Phase n 0 where
  state := after n
  keys := []
  extraAtoms := atomTail n
  context_eq := rfl
  centers_eq := rfl
  raw_eq := rfl
  edges_eq := rfl
  old_keys := by intro _ impossible; cases impossible
  atom_support := by
    intro id seen
    rw [outer_atoms] at seen
    exact Nat.le_of_eq
      (show id = n+1 from by simpa [GeneralNominalState.atomSources,GeneralNominalState.typeSources] using seen)
  focus_generated := .root
  packets_display := by intro _ impossible; cases impossible
  legacy_empty := rfl
  models := fun m => (refresh_models n m).trans (before_models n m)
  reached := ⟨before n,GeneralObservedLadderRefresh301.initial n,.tail .refl (actual n)⟩

def advanceFromRefresh (n : Nat) (k : Nat) (bound : k ≤ n+1) : Phase n k :=
  match k with
  | 0 => ready n
  | k+1 => advance (advanceFromRefresh n k (by omega)) (by omega)

theorem step (n k : Nat) (hi : k ≤ n) :
    (boundary roles).Step registry displayRoot (advanceFromRefresh n k (by omega)).state
      (advanceFromRefresh n (k+1) (by omega)).state :=
  GeneralObservedLadderEnabled301.actual (advanceFromRefresh n k (by omega)) hi

theorem trace (n k : Nat) (cap : k ≤ n+1) :
    Steps ((boundary roles).Step registry displayRoot) (before n) (advanceFromRefresh n k cap).state := by
  induction k with
  | zero => exact .tail .refl (actual n)
  | succ k ih => exact .tail (ih (by omega)) (step n k (by omega))

theorem keys_installed (n k : Nat) (cap : k ≤ n+1) (i : Nat) (past : i < k) :
    GeneralNominalVersionedAllocation231.keys compiled (invocation n i) [(0,(i+1,i+1))] ⊆
      (advanceFromRefresh n k cap).keys := by
  induction k with
  | zero => omega
  | succ k ih =>
    intro key member
    change key ∈ (advanceFromRefresh n k (by omega)).keys ++
      allocated (stagePlan (advanceFromRefresh n k (by omega)) (by omega)).packet
    apply List.mem_append.mpr
    by_cases earlier : i < k
    · exact .inl (ih (by omega) earlier member)
    · right
      have atK : i = k := by omega
      subst i
      unfold allocated
      rw [stage_bindings (advanceFromRefresh n k (by omega)) (by omega)]
      exact member

abbrev settled (n : Nat) := advanceFromRefresh n (n+1) (Nat.le_refl _)

theorem list_frame (n i : Nat) (hi : i ≤ n) :
    Frame compiled (settled n).state.core (focus n i) 1 (replay (settled n) i hi) := by
  let p := settled n
  refine ⟨rfl,p.context_eq.symm,rfl,rfl,?_,?_,List.mem_cons_of_mem _ (List.mem_cons_self ..),rfl,?_,?_⟩
  · change GeneralNominalDemandMerging.pointSite (focus n i) ∈ p.state.core.erased.current.sites
    rw [p.raw_eq,← observed n i]
    exact List.mem_map.mpr ⟨site n i,(sites_exact ..).mpr ⟨i,by omega,rfl⟩,rfl⟩
  · change site n i ∈ p.state.core.sites
    rw [p.centers_eq]
    exact (sites_exact ..).mpr ⟨i,by omega,rfl⟩
  · exact GeneralObservedLadderSelection301.located n i (invocation n i) (by omega)
  · rw [p.context_eq]
    exact replay_prepared p i hi (keys_installed n (n+1) (Nat.le_refl _) i (by omega))

theorem list_instance (n i : Nat) (hi : i ≤ n) (m : Assignment) (valid : Models (settled n).state m) :
    Instance compiled (settled n).state.core m (focus n i) 1 [focus n (i+1)] := by
  let p := settled n
  refine ⟨_,GeneralNominalVersionedEvidence231.certificate_of_semantics
    (list_frame n i hi) (replay_children p i hi).symm (replay_held p i hi m valid) ?_ ?_⟩
  · intro _ seen
    rw [GeneralObservedLadderStage301.current_requests p] at seen
    cases seen
  · exact GeneralRebaseDisplayFrame276.classes_empty (GeneralObservedLadderStage301.current_requests p _) _ m

theorem evidence (n remaining : Nat) (cap : remaining ≤ n+1) (m : Assignment)
    (valid : Models (settled n).state m) :
    (boundary roles).Evidence registry (settled n).state m (focus n (n+1-remaining)) (dictionary remaining) := by
  induction remaining with
  | zero =>
    exact GeneralNominalVersionedEvidence231.evidence_leaf
      (GeneralObservedLadderLeaf301.terminal_instance (settled n) m valid)
  | succ remaining ih =>
    have next : n+1-(remaining+1)+1 = n+1-remaining := by omega
    have child := ih (by omega)
    rw [← next] at child
    exact GeneralNominalVersionedEvidence231.evidence_node
      (list_instance n (n+1-(remaining+1)) (by omega) m valid) (.cons child .nil)

theorem completed_trace (n : Nat) :
    (boundary roles).Step registry displayRoot (before n) (after n) ∧
      Steps ((boundary roles).Step registry displayRoot) (before n) (settled n).state ∧
      GeneralNominalSaturationState.Generated (settled n).state.core.erased.current displayRoot (focus n (n+1)) ∧
      (∀ m, Models (settled n).state m ↔ Models (before n) m) ∧
      ∀ m, Models (settled n).state m →
        (boundary roles).Evidence registry (settled n).state m displayRoot (dictionary (n+1)) := by
  refine ⟨actual n,trace n (n+1) (Nat.le_refl _),(settled n).focus_generated,
    (fun m => ((settled n).models m).trans (before_models n m).symm),?_⟩
  intro m valid
  change (boundary roles).Evidence registry (settled n).state m (focus n 0) (dictionary (n+1))
  simpa only [Nat.sub_self] using evidence n (n+1) (Nat.le_refl _) m valid

end Yulang.GeneralObservedLadderRefreshChain301
