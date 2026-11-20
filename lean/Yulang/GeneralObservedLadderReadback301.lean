import Yulang.GeneralObservedLadderObserver301
import Yulang.B4SkeletonV8

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralObservedLadderReadback301
open GeneralObservedLadderRoute301 (focus)
open GeneralObservedLadderEvidence301 (final dictionary list_instance)
open GeneralObservedLadderObserver301
open GeneralObservedLadderOnlyInstall301 (generated)
open GeneralObservedLadderExact301 (halted)
open GeneralObservedLadderLocal301 (list_local leaf_local)
open GeneralObservedLadderLeaf301 (terminal_instance)
open GeneralNominalExamples (registry displayRoot)
open GeneralDeclarationExamples (roles)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalVersionedJournal232 (Models)
open GeneralGeneratedDictionaryNodes299 (Nodes)
open GeneralGeneratedDictionaryRun299 (run collect)
open CommonRoleOutermostResolver (Dictionary Frontier)
open GeneralNominalCommonBridge (Assignment)
open B4TargetV8 (Classify local_functional)

theorem run_branch (n i : Nat) (hi : i ≤ n) (gas : Nat) :
    run (table n) (gas+1) i =
      (run (table n) gas (i+1)).map (fun d => .node 1 [d]) := by
  rw [run,branch n i hi]
  cases hit : run (table n) gas (i+1) <;> simp [collect,hit]

theorem fuel_exact (n depth : Nat) (cap : depth ≤ n+1) (gas : Nat) :
    run (table n) gas (n+1-depth) =
      if depth < gas then some (dictionary depth) else none := by
  induction depth generalizing gas with
  | zero =>
    rw [Nat.sub_zero]
    cases gas with
    | zero => rfl
    | succ gas => rw [run,leaf n]; rfl
  | succ depth ih =>
    cases gas with
    | zero => rfl
    | succ gas =>
      have below : n+1-(depth+1) ≤ n := by omega
      have next : n+1-(depth+1)+1 = n+1-depth := by omega
      rw [run_branch n _ below, next,ih (by omega)]
      by_cases enough : depth < gas
      · have more : depth+1 < gas+1 := by omega
        rw [ite_eq_left enough,ite_eq_left more]
        rfl
      · have notMore : ¬ depth+1 < gas+1 := by omega
        rw [ite_eq_right enough,ite_eq_right notMore]
        rfl

theorem first_success (n i : Nat) (cap : i ≤ n+1) (gas : Nat) :
    (∃ d, run (table n) gas i = some d) ↔ n+1-i < gas := by
  have exact := fuel_exact n (n+1-i) (by omega) gas
  have back : n+1-(n+1-i) = i := by omega
  rw [back] at exact
  rw [exact]
  by_cases enough : n+1-i < gas <;> simp [enough]

theorem computed (n : Nat) : run (table n) (n+2) 0 = some (dictionary (n+1)) := by
  have actual := fuel_exact n (n+1) (Nat.le_refl _) (n+2)
  rwa [Nat.sub_self,ite_eq_left (by omega)] at actual

theorem nodes (n : Nat) :
    Nodes (boundary roles) registry (final n).state (table n) (focus n) := by
  intro i row hit m valid ds children
  rcases entries n i row hit with ⟨hi,rfl⟩|⟨rfl,rfl⟩
  · exact GeneralNominalVersionedEvidence231.evidence_node
      (list_instance n (n+1) (Nat.le_refl _) i (by omega) m valid) children
  · exact GeneralNominalVersionedEvidence231.evidence_node
      (terminal_instance (final n) m valid) children

theorem exact_compiled_root (n : Nat) (d : Dictionary) :
    Classify (boundary roles) registry (final n).state displayRoot (.selected d) ↔ d = dictionary (n+1) := by
  change Classify (boundary roles) registry (final n).state (focus n 0) (.selected d) ↔ _
  rw [← exact_on_present n 0 (branch n 0 (Nat.zero_le _)) d,computed]
  exact ⟨fun eq => (Option.some.inj eq).symm,fun eq => by rw [eq]⟩

theorem compiler_sound (n i gas : Nat) (d : Dictionary) (pass : run (table n) gas i = some d)
    (m : Assignment) (valid : Models (final n).state m) :
    (boundary roles).Evidence registry (final n).state m (focus n i) d :=
  GeneralGeneratedDictionaryNodes299.same_model (b:=boundary roles) (r:=registry) (s:=(final n).state)
    (table n) (focus n) (nodes n) m valid gas i d pass

theorem evidence_at (n : Nat) : B4SkeletonV8.EvidenceAt (boundary roles) registry (final n).state displayRoot := by
  intro m valid o key children ds reached _ _ selected childEvidence
  have within : ∃ i ≤ n+1, o = focus n i := by
    rcases reached with rfl|there
    · exact ⟨0,by omega,rfl⟩
    · exact generated (final n) there
  obtain ⟨i,cap,rfl⟩ := within
  by_cases hi : i ≤ n
  · obtain ⟨rfl,rfl⟩ := Frontier.selected.inj (local_functional selected (list_local n i hi))
    exact GeneralNominalVersionedEvidence231.evidence_node
      (list_instance n (n+1) (Nat.le_refl _) i (by omega) m valid) childEvidence
  have last : i = n+1 := by omega
  subst i
  obtain ⟨rfl,rfl⟩ := Frontier.selected.inj (local_functional selected (leaf_local n))
  exact GeneralNominalVersionedEvidence231.evidence_node (terminal_instance (final n) m valid) childEvidence

theorem selection_graph_accessible (n i : Nat) (cap : i ≤ n+1) :
    Acc (CommonRoleOutermostResolver.Child (B4TargetV8.Local (boundary roles) registry (final n).state)) (focus n i) := by
  have depth : n+1-(n+1-i) = i := by omega
  have computed := fuel_exact n (n+1-i) (by omega) (n+2)
  rw [depth,ite_eq_left (by omega)] at computed
  have hit : ∃ e, table n i = some e := by
    by_cases hi : i ≤ n
    · exact ⟨_,branch n i hi⟩
    · have last : i = n+1 := by omega
      subst i
      exact ⟨_,leaf n⟩
  obtain ⟨e,seen⟩ := hit
  exact GeneralGeneratedSelectedExact299.derivation_accessible _ _ ((exact_on_present n i seen _).mp computed)

end Yulang.GeneralObservedLadderReadback301
