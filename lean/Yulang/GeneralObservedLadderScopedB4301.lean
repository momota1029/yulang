import Yulang.GeneralObservedLadderJournalCompiler301

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 27000
set_option maxHeartbeats 8500000
namespace Yulang.GeneralObservedLadderScopedB4301
open GeneralObservedLadderInitial301 (initial)
open GeneralObservedLadderAdvance301 (run phase_step)
open GeneralObservedLadderExact301 (halted reachable_phases accessible_phase)
open GeneralObservedLadderRoute301
open GeneralObservedLadderLedger301
open GeneralObservedLadderEvidence301 (final dictionary)
open GeneralObservedLadderOnlyInstall301 (generated)
open GeneralObservedLadderReadback301 (exact_compiled_root evidence_at)
open GeneralObservedLadderLocal301 (list_local leaf_local)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary closure)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralDeclarationExamples (roles)
open GeneralNominalExamples (registry displayRoot)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalSaturationState (Generated)
open CommonRoleOutermostResolver (Dictionary Frontier)
open B4Target (Steps)
open B4TargetV8 (Local Classify)

theorem suffix_generated (p : Phase n k) (i j : Nat) (low : i ≤ j) (high : j ≤ k) :
    Generated p.state.core.erased.current (focus n i) (focus n j) := by
  induction j with
  | zero =>
    have same : i = 0 := by omega
    subst i
    exact .root
  | succ j ih =>
    by_cases same : i = j+1
    · subst i
      exact .root
    · apply Generated.child (ih (by omega) (by omega))
      rw [p.edges_eq]
      exact (edge_exact ..).mpr ⟨j,by omega,rfl⟩

theorem not_stable_before (n k : Nat) (before : k ≤ n) (i : Nat) (hi : i ≤ k) :
    ¬ (boundary roles).Stable registry (run n k (by omega)).state (focus n i) := by
  intro stable
  let p := run n k (by omega)
  let effect := GeneralObservedLadderEnabled301.effect p before
  exact stable (focus n k) (suffix_generated p i k hi (Nat.le_refl _)) _
    (.install effect (GeneralObservedLadderEnabled301.enabled p before)
      (GeneralObservedLadderEnabled301.not_committed p before))

theorem stable_iff_final (n k : Nat) (cap : k ≤ n+1) (i : Nat) (hi : i ≤ k) :
    (boundary roles).Stable registry (run n k cap).state (focus n i) ↔ k = n+1 := by
  constructor
  · intro stable
    by_cases before : k ≤ n
    · exact False.elim (not_stable_before n k before i hi stable)
    · omega
  · rintro rfl
    have finished := closure (halted n)
    exact finished.2 (focus n i) (suffix_generated (final n) 0 i (Nat.zero_le _) hi)

theorem evidence_at_phases (n k : Nat) (cap : k ≤ n+1) :
    B4SkeletonV8.EvidenceAt (boundary roles) registry (run n k cap).state displayRoot := by
  by_cases terminal : k = n+1
  · subst k
    exact evidence_at n
  let p := run n k cap
  intro m valid o key children ds reached stable _ _ _
  have within : ∃ i ≤ k, o = focus n i := by
    rcases reached with rfl|given
    · exact ⟨0,Nat.zero_le _,rfl⟩
    · exact generated p given
  obtain ⟨i,hi,rfl⟩ := within
  exact False.elim (terminal ((stable_iff_final n k cap i hi).mp stable))

theorem evidence_at_reachable (n : Nat) (s : State roles)
    (fromThisInitial : Steps ((boundary roles).Step registry displayRoot) (initial n) s) :
    B4SkeletonV8.EvidenceAt (boundary roles) registry s displayRoot := by
  obtain ⟨k,cap,rfl⟩ := reachable_phases n s fromThisInitial
  exact evidence_at_phases n k cap

theorem generated_children_at_reachable (n : Nat) (s : State roles)
    (fromThisInitial : Steps ((boundary roles).Step registry displayRoot) (initial n) s)
    (o : Occurrence roles) (inScope : o = displayRoot ∨ (boundary roles).Generated registry s displayRoot o)
    (stable : (boundary roles).Stable registry s o) (key : Nat) (children : List (Occurrence roles))
    (selected : Local (boundary roles) registry s o (.selected key children)) :
    ∀ c ∈ children, (boundary roles).Generated registry s displayRoot c := by
  obtain ⟨k,cap,rfl⟩ := reachable_phases n s fromThisInitial
  let p := run n k cap
  have within : ∃ i ≤ k, o = focus n i := by
    rcases inScope with rfl|given
    · exact ⟨0,Nat.zero_le _,rfl⟩
    · exact generated p given
  obtain ⟨i,atStage,rfl⟩ := within
  have terminal : k = n+1 := (stable_iff_final n k cap i atStage).mp stable
  subst k
  by_cases hi : i ≤ n
  · obtain ⟨_,rfl⟩ := Frontier.selected.inj (B4TargetV8.local_functional selected (list_local n i hi))
    intro child member
    cases List.mem_singleton.mp member
    exact suffix_generated (final n) 0 (i+1) (by omega) (by omega)
  have last : i = n+1 := by omega
  subst i
  obtain ⟨_,rfl⟩ := Frontier.selected.inj (B4TargetV8.local_functional selected (leaf_local n))
  intro _ impossible
  cases impossible

theorem closure_of_any_terminal (n : Nat) (s : State roles)
    (path : Steps ((boundary roles).Step registry displayRoot) (initial n) s)
    (noMore : ∀ next, ¬ (boundary roles).Step registry displayRoot s next) :
    s = (final n).state := by
  obtain ⟨k,cap,rfl⟩ := reachable_phases n s path
  by_cases before : k ≤ n
  · exact False.elim (noMore _ (phase_step n k before))
  have eq : k = n+1 := by omega
  subst k
  rfl

theorem compiled_at_terminal (n : Nat) (s : State roles)
    (path : Steps ((boundary roles).Step registry displayRoot) (initial n) s)
    (noMore : ∀ next, ¬ (boundary roles).Step registry displayRoot s next)
    (d : Dictionary) :
    (Classify (boundary roles) registry s displayRoot (.selected d) ↔ d = dictionary (n+1)) ∧
    (∀ m, Models s m → (boundary roles).Evidence registry s m displayRoot (dictionary (n+1))) := by
  rw [closure_of_any_terminal n s path noMore]
  exact ⟨exact_compiled_root n d,GeneralObservedLadderEvidence301.root n⟩

end Yulang.GeneralObservedLadderScopedB4301
