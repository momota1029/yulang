import Yulang.GeneralDeferredLadderVariantExact302

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeferredLadderOutcomes302
open GeneralDeferredLadderAfterVariants302 (OwnedPhase variantOwned advanceFrom path_count)
open GeneralDeferredLadderVariantExact302 (frame halted)
open GeneralDeferredLadderAdvance302 (run)
open GeneralDeferredLadderTrace302 (InstallTrace prefix_exists)
open GeneralDeferredLadderExact302 (RawStep)
open GeneralDeferredLadderBranch302 (successor)
open GeneralObservedLadderRefresh301 (before)
open GeneralObservedLadderRoute301 (focus)
open GeneralObservedLadderEvidence301 (dictionary replay_held replay_children)
open GeneralObservedLadderPlan301 (compiled)
open GeneralObservedLadderRefreshProgram301 (terminal_table)
open GeneralObservedLadderBudget301 (Counted)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedEvidence231 (Instance)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalExamples (registry displayRoot)
open GeneralDeclarationExamples (roles)
open GeneralGeneratedDictionaryRun299
open GeneralObservedLadderJournalCompiler301 (table)
open B4Target (Steps)

theorem list_instance (p : OwnedPhase n k) (i : Nat) (past : i < k) (hi : i ≤ n)
    (m : Assignment) (held : Models p.state m) :
    Instance compiled p.state.core m (focus n i) 1 [focus n (i+1)] := by
  refine ⟨_,GeneralNominalVersionedEvidence231.certificate_of_semantics
    (frame p i past hi) (replay_children p.toPhase i hi).symm (replay_held p.toPhase i hi m held) ?_ ?_⟩
  · intro _ seen
    rw [GeneralObservedLadderStage301.current_requests p.toPhase] at seen
    cases seen
  · exact GeneralRebaseDisplayFrame276.classes_empty
      (GeneralObservedLadderStage301.current_requests p.toPhase _) _ m

theorem evidence (p : OwnedPhase n (n+1)) (depth : Nat) (cap : depth ≤ n+1)
    (m : Assignment) (valid : Models p.state m) :
    (boundary roles).Evidence registry p.state m (focus n (n+1-depth)) (dictionary depth) := by
  induction depth with
  | zero =>
    exact GeneralNominalVersionedEvidence231.evidence_leaf
      (GeneralObservedLadderLeaf301.terminal_instance p.toPhase m valid)
  | succ depth ih =>
    have next : n+1-(depth+1)+1 = n+1-depth := by omega
    have child := ih (by omega)
    rw [← next] at child
    exact GeneralNominalVersionedEvidence231.evidence_node
      (list_instance p (n+1-(depth+1)) (by omega) (by omega) m valid) (.cons child .nil)

theorem root_evidence (p : OwnedPhase n (n+1)) (m : Assignment) (valid : Models p.state m) :
    (boundary roles).Evidence registry p.state m displayRoot (dictionary (n+1)) := by
  change (boundary roles).Evidence registry p.state m (focus n 0) (dictionary (n+1))
  simpa only [Nat.sub_self] using evidence p (n+1) (Nat.le_refl _) m valid

theorem journal (p : OwnedPhase n (n+1)) (fuel : Nat) :
    GeneralGeneratedDictionaryRun299.run (table p.state) fuel 0 =
    if n+1 < fuel then some (dictionary (n+1)) else none := by
  rw [terminal_table p.toPhase]
  have exact := GeneralObservedLadderReadback301.fuel_exact n (n+1) (Nat.le_refl _) fuel
  rwa [Nat.sub_self] at exact

theorem counted_before {n l : Nat} {s t : State roles} (path : InstallTrace n l s t) : Counted l s t := by
  induction path with
  | zero => exact .refl _
  | next _ step _ ih => exact .tail ih step

theorem append {a b : Nat} {s t u : State roles} (one : Counted a s t) (two : Counted b t u) :
    Counted (a+b) s u := by
  induction two with
  | refl => exact one
  | tail _ step ih => exact .tail (ih one) step

def terminal (p : OwnedPhase n k) (cap : k ≤ n+1) : OwnedPhase n (n+1) :=
  (Nat.add_sub_of_le cap) ▸ advanceFrom p (n+1-k) (by omega)

theorem terminal_state (p : OwnedPhase n k) (cap : k ≤ n+1) :
    (terminal p cap).state = (advanceFrom p (n+1-k) (by omega)).state := by
  have same {i j : Nat} (e : i = j) (phase : OwnedPhase n i) :
      ((e ▸ phase : OwnedPhase n j)).state = phase.state := by
    cases e
    rfl
  exact same (Nat.add_sub_of_le cap) _

theorem suffix (p : OwnedPhase n k) (cap : k ≤ n+1) :
    Counted (n+1-k) p.state (terminal p cap).state := by
  rw [terminal_state]
  exact path_count p _ (by omega)

theorem schedule_count (n k : Nat) (cap : k ≤ n+1) (extra : Nat) :
    Counted (n+2) (before n) (terminal (variantOwned n k cap extra) cap).state := by
  have early := counted_before (prefix_exists n k cap)
  have promoted : Counted 1 (run n k cap).state (variantOwned n k cap extra).state :=
    .tail (.refl _) (GeneralDeferredLadderBranch302.actual (run n k cap) extra)
  have complete := append (append early promoted) (suffix (variantOwned n k cap extra) cap)
  have len : k+1+(n+1-k) = n+2 := by omega
  exact len ▸ complete

theorem schedule (n k : Nat) (cap : k ≤ n+1) (extra : Nat) :
    let final := terminal (variantOwned n k cap extra) cap
    Counted (n+2) (before n) final.state ∧
      (∀ next, ¬ RawStep final.state next) ∧
      GeneralGeneratedDictionaryRun299.run (table final.state) (n+2) 0 = some (dictionary (n+1)) ∧
      (∀ m, Models final.state m ↔ Models (before n) m) ∧
      ∀ m, Models final.state m → (boundary roles).Evidence registry final.state m displayRoot (dictionary (n+1)) := by
  let p := terminal (variantOwned n k cap extra) cap
  refine ⟨schedule_count n k cap extra,halted p,?_,
    (fun m => (p.models m).trans (GeneralObservedLadderRefreshChain301.before_models n m).symm),root_evidence p⟩
  rw [journal p]
  exact ite_eq_left (by omega)

theorem infinite_halted_outcomes (n : Nat) :
    ∃ final : Nat → State roles, Function.Injective final ∧ ∀ extra,
      Counted (n+2) (before n) (final extra) ∧
      (∀ t, ¬ RawStep (final extra) t) ∧
      GeneralGeneratedDictionaryRun299.run (table (final extra)) (n+2) 0 = some (dictionary (n+1)) ∧
      (∀ m, Models (final extra) m ↔ Models (before n) m) := by
  let p := run n (n+1) (Nat.le_refl _)
  refine ⟨successor p,GeneralDeferredLadderBranch302.injective p,?_⟩
  intro extra
  let q := variantOwned n (n+1) (Nat.le_refl _) extra
  have early : Counted (n+1) (before n) p.state := counted_before (prefix_exists n (n+1) (Nat.le_refl _))
  have last : Counted 1 p.state (successor p extra) := .tail (.refl _) (GeneralDeferredLadderBranch302.actual p extra)
  have witness : Counted ((n+1)+1) (before n) (successor p extra) := append (a:=n+1) (b:=1) early last
  refine ⟨witness,halted q,?_,fun m => (GeneralDeferredLadderBranch302.models_preserved p extra m).trans (p.models m)⟩
  rw [show successor p extra = q.state from rfl,journal q]
  exact ite_eq_left (by omega)

end Yulang.GeneralDeferredLadderOutcomes302
