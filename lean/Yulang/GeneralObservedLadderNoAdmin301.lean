import Yulang.GeneralObservedLadderEvidence301
import Yulang.GeneralNominalVersionedMixedTerminalStable234
import Yulang.GeneralDictionaryGroundCopy218Refresh

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralObservedLadderNoAdmin301
open GeneralObservedLadderSource301 (snapshot endpoint nominal_at scalar_at models_exact)
open GeneralObservedLadderInitial301 (initial context)
open GeneralObservedLadderReport301 (pos)
open GeneralObservedLadderRoute301
open GeneralObservedLadderLedger301
open GeneralObservedLadderStage301 (model)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedMixedKernel234 (Equal)
open GeneralNominalVersionedMixedTerminalStable234 (HeadlessUnknown EqualityClosed)
open GeneralNominalOutputGrowth (finiteModel finite_prefix_models finite_prefix_separates tower)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
open GeneralNominalRecursiveInspection (Test)
open GeneralDeclarationExamples (roles)
open GeneralNominalExamples (displayRoot)

def padding (n : Nat) (alter : Nat → Ty) : Assignment := fun i =>
  if i ≤ n+1 then finiteModel n i else (alter i,Common.rowEmpty)

theorem fixed (n : Nat) (alter : Nat → Ty) (i : Nat) (low : i ≤ n+1) :
    padding n alter i = finiteModel n i :=
  ite_eq_left low

theorem free (n : Nat) (alter : Nat → Ty) (i : Nat) (high : n+1 < i) :
    (padding n alter i).1 = alter i := by
  unfold padding
  rw [ite_eq_right (Nat.not_le_of_gt high)]

theorem snapshot_padded (n : Nat) (alter : Nat → Ty) :
    GeneralNominalState.Models (snapshot n) (padding n alter) := by
  apply (models_exact n _).mpr
  constructor
  · intro i earlier
    rw [fixed n alter i (by omega),fixed n alter (i+1) (by omega)]
    exact finite_prefix_models n i earlier
  · rw [fixed n alter (n+1) (Nat.le_refl _)]
    exact GeneralObservedLadderSource301.scalar_model n _ (GeneralObservedLadderSource301.model_exists n)

theorem padded (p : Phase n k) (alter : Nat → Ty) : Models p.state (padding n alter) := by
  apply (p.models _).mpr
  exact (GeneralNominalVersionedJournal232.initial_models ..).mpr
    ⟨snapshot_padded n alter,GeneralNominalCenters.point_root_holds _ displayRoot (fun _ => rfl) _⟩

theorem all_known (p : Phase n k) (i : Nat) (bound : i ≤ n+1) :
    GeneralNominalState.Known p.state.core.erased.current.context.state i := by
  rw [p.context_eq]
  refine ⟨pos n i bound,rfl,?_⟩
  by_cases inner : i ≤ n
  · exact .inr ⟨_,nominal_at n i inner⟩
  · left
    have eq : i = n+1 := by omega
    subst i
    change ((snapshot n).view.heads (endpoint n)).node ≠ .unresolved
    rw [scalar_at]
    intro impossible
    cases impossible

theorem headless (p : Phase n k) : HeadlessUnknown p.state := by
  refine ⟨padding n (fun _ => .top),padded p _,?_⟩
  intro id _ unknown test held
  have large : n+1 < id := by
    by_cases low : id ≤ n+1
    · exact False.elim (unknown (all_known p id low))
    · omega
  rw [free _ _ _ large] at held
  exact GeneralDictionaryGroundCopy218Refresh.top_no_head test held

theorem tower_not_top (d : Nat) : ¬ Equivalent .top (tower d) := by
  intro eq
  cases d with
  | zero => exact GeneralDictionaryGroundCopy218Refresh.top_no_head (.scalar .int) eq
  | succ k =>
    exact GeneralDictionaryGroundCopy218Refresh.top_no_head (.nominal 0 1)
      ⟨[.inl (tower k)],rfl,eq⟩

def mark (n id : Nat) : Nat → Ty := fun name => if name = id then .top else (finiteModel n name).1

theorem isolate (n a b : Nat) (large : n+1 < a) (apart : a ≠ b) :
    ¬ Equivalent (padding n (mark n a) a).1 (padding n (mark n a) b).1 := by
  intro eq
  rw [free _ _ _ large] at eq
  have right : (padding n (mark n a) b).1 = (finiteModel n b).1 := by
    by_cases small : b ≤ n+1
    · rw [fixed _ _ _ small]
    · rw [free _ _ _ (Nat.lt_of_not_ge small)]
      exact ite_eq_right (Ne.symm apart)
  rw [right] at eq
  have top : mark n a a = .top := ite_eq_left rfl
  rw [top] at eq
  exact tower_not_top (n+1-b) eq

theorem only_equal_names (p : Phase n k) (a b : Nat) (same : Equal p.state a b) : a = b := by
  by_cases apart : a = b
  · exact apart
  by_cases aHigh : n+1 < a
  · exact False.elim (isolate n a b aHigh apart (same _ (padded p _)))
  by_cases bHigh : n+1 < b
  · have inverse := same _ (padded p (mark n b))
    exact False.elim (isolate n b a bHigh (Ne.symm apart) ⟨inverse.2,inverse.1⟩)
  exact False.elim (finite_prefix_separates n a b (by omega) (by omega) apart (same _ (model p)))

theorem equality_closed (p : Phase n k) : EqualityClosed p.state := by
  intro a b _ _ same
  cases only_equal_names p a b same
  intro _ _
  exact ⟨subtype_refl _,subtype_refl _⟩

theorem point_closed (p : Phase n k) :
    GeneralNominalReobservationSteps.PointClosed p.state.core.erased.current.context.state := by
  rw [p.context_eq]
  intro slot descriptor recorded
  change (if h : slot.val ≤ n then some (GeneralNominalOutputGrowthModels.descriptor n slot h) else none) =
    some descriptor at recorded
  split at recorded
  · cases Option.some.inj recorded
    intro param member
    cases List.mem_singleton.mp member
    rfl
  · cases recorded

end Yulang.GeneralObservedLadderNoAdmin301
