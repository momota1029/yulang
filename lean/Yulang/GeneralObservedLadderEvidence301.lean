import Yulang.GeneralObservedLadderLeaf301
import Yulang.GeneralDepthTwoFrameCarry300

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 27000
set_option maxHeartbeats 9000000
namespace Yulang.GeneralObservedLadderEvidence301
open GeneralObservedLadderSource301 (snapshot)
open GeneralObservedLadderInitial301 (context initial)
open GeneralObservedLadderReport301 (point exact_at)
open GeneralObservedLadderPlan301 (compiled)
open GeneralObservedLadderRoute301
open GeneralObservedLadderLedger301
open GeneralObservedLadderAdvance301 (run phase_step)
open GeneralObservedLadderStage301 (metadata model current_requests)
open GeneralObservedLadderLeaf301 (terminal_instance)
open GeneralDeclarationExamples (roles display)
open GeneralNominalExamples (registry displayRoot)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedEvidence231 (Frame Instance)
open GeneralNominalVersionedCandidates231 (Prepared)
open GeneralNominalVersionedPlans231 (Holds)
open GeneralNominalVersionedFrame231 (children)
open GeneralNominalVersionedInstallation231 (allocated)
open GeneralNominalVersionedTransport231 (extendedPlan)
open GeneralNominalIdentities (Origin source)
open CommonRoleOutermostResolver (Dictionary)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)

theorem keys_installed (n k : Nat) (cap : k ≤ n+1) (i : Nat) (past : i < k) :
    GeneralNominalVersionedAllocation231.keys compiled (invocation n i) [(0,(i+1,i+1))] ⊆ (run n k cap).keys := by
  induction k with
  | zero => omega
  | succ k ih =>
    intro key member
    change key ∈ (run n k (by omega)).keys ++ allocated (stagePlan (run n k (by omega)) (by omega)).packet
    apply List.mem_append.mpr
    by_cases earlier : i < k
    · exact .inl (ih (by omega) earlier member)
    · right
      have atK : i = k := by omega
      subst i
      unfold allocated
      rw [stage_bindings (run n k (by omega)) (by omega)]
      exact member

abbrev replay (p : Phase n k) (i : Nat) (hi : i ≤ n) :=
  extendedPlan (p.keys.map (source (n+1))) p.extraAtoms p.keys (basePlan n i hi)

theorem replay_held (p : Phase n k) (i : Nat) (hi : i ≤ n) (m : Assignment) (valid : Models p.state m) :
    Holds (replay p i hi) m := by
  have whole := valid.1.1
  rw [p.context_eq] at whole
  obtain ⟨old,extra⟩ := (GeneralDictionaryOrdinaryTransport.models_extended ..).mp whole
  exact (GeneralNominalVersionedTransport231.holds_iff ..).mpr
    ⟨GeneralObservedLadderSemantics301.holds n i (invocation n i) hi m old,extra⟩

theorem replay_children (p : Phase n k) (i : Nat) (hi : i ≤ n) :
    children (replay p i hi).packet = [focus n (i+1)] :=
  (GeneralNominalVersionedTransport231.children_eq ..).trans
    ((GeneralObservedLadderSelection301.one_child n i (invocation n i) hi).trans
      (congrArg (fun s : GeneralNominalCenters.Site roles => [s.occurrence]) (child_site n i hi)))

theorem replay_prepared (p : Phase n k) (i : Nat) (hi : i ≤ n)
    (owned : GeneralNominalVersionedAllocation231.keys compiled (invocation n i) [(0,(i+1,i+1))] ⊆ p.keys) :
    Prepared compiled (env p) (focus n i) display := by
  have base := GeneralObservedLadderSelection301.prepared n i (invocation n i) hi
  have located := GeneralObservedLadderSelection301.located n i (invocation n i) (by omega)
  have reportBindings : GeneralNominalRecursiveInspection.bindings (snapshot n)
      (GeneralNominalRecursiveCandidates.report (context n) display [point n i (by omega)]) = [(0,(i+1,i+1))] :=
    GeneralObservedLadderPlan301.bindings n i (invocation n i) hi
  have witness := GeneralNominalVersionedPlans231.head_models (replay_held p i hi _ (model p))
  refine GeneralDepthTwoFrameCarry300.prepared_carried _ _ _ (context n) compiled (focus n i) display _ base located ?_ ?_
  · rw [reportBindings]
    exact owned
  · exact ⟨_,witness⟩

theorem replay_frame (n k : Nat) (cap : k ≤ n+1) (i : Nat) (past : i < k) :
    Frame compiled (run n k cap).state.core (focus n i) 1
      (replay (run n k cap) i (by omega)) := by
  let p := run n k cap
  refine ⟨rfl,p.context_eq.symm,rfl,rfl,?_,?_,List.mem_cons_of_mem _ (List.mem_cons_self ..),rfl,?_,?_⟩
  · change GeneralNominalDemandMerging.pointSite (focus n i) ∈ p.state.core.erased.current.sites
    rw [p.raw_eq,← observed n i]
    exact List.mem_map.mpr ⟨site n i,(sites_exact ..).mpr ⟨i,Nat.le_of_lt past,rfl⟩,rfl⟩
  · change site n i ∈ p.state.core.sites
    rw [p.centers_eq]
    exact (sites_exact ..).mpr ⟨i,Nat.le_of_lt past,rfl⟩
  · exact GeneralObservedLadderSelection301.located n i (invocation n i) (by omega)
  · rw [p.context_eq]
    exact replay_prepared p i (by omega) (keys_installed n k cap i past)

theorem list_instance (n k : Nat) (cap : k ≤ n+1) (i : Nat) (past : i < k)
    (m : Assignment) (valid : Models (run n k cap).state m) :
    Instance compiled (run n k cap).state.core m (focus n i) 1 [focus n (i+1)] := by
  let p := run n k cap
  refine ⟨_,GeneralNominalVersionedEvidence231.certificate_of_semantics
    (replay_frame n k cap i past) (replay_children p i (by omega)).symm
    (replay_held p i (by omega) m valid) ?_ ?_⟩
  · intro output seen
    rw [current_requests p] at seen
    cases seen
  · exact GeneralRebaseDisplayFrame276.classes_empty (current_requests p _) _ m

def dictionary : Nat → Dictionary
  | 0 => .node 3 []
  | depth+1 => .node 1 [dictionary depth]

abbrev final (n : Nat) := run n (n+1) (Nat.le_refl _)

theorem node (n depth : Nat) (cap : depth ≤ n+1) (m : Assignment) (valid : Models (final n).state m) :
    (boundary roles).Evidence registry (final n).state m (focus n (n+1-depth)) (dictionary depth) := by
  induction depth with
  | zero =>
    exact GeneralNominalVersionedEvidence231.evidence_leaf (terminal_instance (final n) m valid)
  | succ depth ih =>
    have before : n+1-(depth+1) < n+1 := by omega
    have next : n+1-(depth+1)+1 = n+1-depth := by omega
    have child := ih (by omega)
    rw [← next] at child
    exact GeneralNominalVersionedEvidence231.evidence_node
      (list_instance n (n+1) (Nat.le_refl _) (n+1-(depth+1)) before m valid)
      (.cons child .nil)

theorem root (n : Nat) (m : Assignment) (valid : Models (final n).state m) :
    (boundary roles).Evidence registry (final n).state m displayRoot (dictionary (n+1)) := by
  change (boundary roles).Evidence registry (final n).state m (focus n 0) (dictionary (n+1))
  simpa only [Nat.sub_self] using node n (n+1) (Nat.le_refl _) m valid

theorem actual_with_dictionary (n : Nat) :
    B4Target.Steps ((boundary roles).Step registry displayRoot) (initial n) (final n).state ∧
      B4TargetV8.Reachable (boundary roles) registry displayRoot (final n).state ∧
      (∃ m, Models (final n).state m) ∧
      (∀ m, Models (final n).state m ↔ Models (initial n) m) ∧
      ∀ m, Models (final n).state m →
        (boundary roles).Evidence registry (final n).state m displayRoot (dictionary (n+1)) :=
  ⟨GeneralObservedLadderAdvance301.path n (n+1) (Nat.le_refl _),(final n).reached,
    ⟨_,model (final n)⟩,(final n).models,root n⟩

end Yulang.GeneralObservedLadderEvidence301
