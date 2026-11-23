import Yulang.GeneralDeclarativeWitnessMixedForwardFixture361

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 68000
set_option maxHeartbeats 70000000
namespace Yulang.GeneralDeclarativeWitnessMixedForwardSound361
open GeneralDeclarativeWitnessMixedForwardFixture361 (PairOfNodes run verify start actual_aligned_two_nodes)
open GeneralDeclarativeWitnessMixedForwardChoice361 (only_reads_two_distinct_source_lanes compiler_uses_same_selected_clause)
open GeneralDeclarativeWitnessNestedModel361 (state model model_fits composed_leaf_sound)
open GeneralDeclarativeWitnessNativeInstall360 (Fits NativeViews interpreted)
open GeneralDeclarativeWitnessReleasedForward360 (forwardDemand knownTarget)
open GeneralDeclarativeWitnessJointObservation359 (secondLo secondHi)
open GeneralDeclarativeWitnessNativeNestedMatch361 (Meaning values)
open GeneralDeclarativeWitnessNativePortTransport361 (Part view)
open GeneralDeclarativeWitnessSequentialNative360 (Sequence sequence)
open GeneralDeclarativeWitnessNestedInstall360 (Run)
open GeneralDeclarativeEntailment320 (Holds)
open GeneralDeclarativeBounds319 (bound_sound)
open GeneralDeclarativeGrowth327 (restrict)
open GeneralDeclarativeWitnessLiteral349 (preserves_iff)
open GeneralDeclarativeDemand320 (Demand)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Equivalent Subtype)
open CommonRoleOutermostResolver (Frontier Classify)

inductive Local {negative : Bool} {r : Run negative} {s : Sequence r}
    (p : PairOfNodes s) : Demand → Frontier Demand → Prop where
  | parent : Local p forwardDemand (.selected p.parent.impl.id [s.receiver])
  | child : Local p s.receiver (.selected p.leaf.chosen.impl.id [])

theorem recursive_witness {negative} {r : Run negative} {s : Sequence r} (p : PairOfNodes s) :
    Classify (Local p) forwardDemand (.selected (.node p.parent.impl.id [.node p.leaf.chosen.impl.id []])) := by
  refine ⟨.selected p.parent.impl.id [.selected p.leaf.chosen.impl.id []],?_,?_⟩
  · exact .selected .parent (.cons (.selected .child .nil) .nil)
  · exact .selected (.cons (.selected .nil (.selected rfl)) .nil) (.selected rfl)

theorem ordered_dictionary_sound {negative} {r : Run negative} {s : Sequence r} (p : PairOfNodes s)
    (m : Assignment) (v : NativeViews) (fit : Fits p.leaf.result.world m v) :
    Classify (Local p) forwardDemand (.selected (.node p.parent.impl.id [.node p.leaf.chosen.impl.id []])) ∧
    s.continuation.impl = p.parent.impl ∧ s.continuation.kids = [s.receiver] ∧
    p.leaf.result.prep.impl = p.leaf.chosen.impl ∧
    v knownTarget.center = some (r.typed.write.code.eval m) ∧
    Equivalent (m 65).1 (GeneralDeclarativeWitnessOpenSpine359.sem m (secondLo.code 65)) ∧
    Equivalent (m 66).1 (GeneralDeclarativeWitnessOpenSpine359.sem m (secondHi.code 66)) ∧
    Subtype (m 65).1 (m 67).1 ∧ Subtype (m 67).1 (m 66).1 ∧
    (∀ which : Part, ∃ seen,view p.leaf.origin v which = some seen ∧
      Meaning r.env seen p.leaf.chosen.pattern (values m p.leaf.chosen.captures)) := by
  have beforeLeaf : Fits s.final m v :=
    ⟨restrict ((preserves_iff ..).mp p.leaf.result.kept) m fit.1,fit.2⟩
  have beforeParent : Fits s.ordinaryChild.final m v :=
    ⟨(GeneralDeclarativeWitnessNativePreparation360.same_model_of_prepared s.continuation m beforeLeaf.1).1,fit.2⟩
  have inputs := only_reads_two_distinct_source_lanes p.parent m v beforeParent
  have child := composed_leaf_sound p.leaf m v fit
  have orders := compiler_uses_same_selected_clause p.parent
  exact ⟨recursive_witness p,orders.1,orders.2.1,child.2.2.1,inputs.1,inputs.2.1,inputs.2.2,
    bound_sound m beforeParent.1.1 p.parent.grounded.left,
    bound_sound m beforeParent.1.1 p.parent.grounded.right,child.2.1⟩

theorem actual_mixed_pair_has_one_fitting_model (negative : Bool) :
    ∃ (r : Run negative) (s : Sequence r) (p : PairOfNodes s),
      start negative = some r ∧ sequence r = some s ∧ run s = some p ∧
      p.parent.impl.id = 74 ∧ p.leaf.chosen.impl.id = 75 ∧
      Classify (Local p) forwardDemand (.selected (.node 74 [.node 75 []])) ∧
      (∀ upper scalar,Fits p.leaf.result.world (model upper scalar) (interpreted p.leaf.result.world.board (model upper scalar))) ∧
      (∀ m v,Fits p.leaf.result.world m v →
        v knownTarget.center = some (r.typed.write.code.eval m) ∧ Holds m ⟨105,.variable 61⟩ ∧
        ∀ which : Part, ∃ seen,view p.leaf.origin v which = some seen ∧
          Meaning r.env seen p.leaf.chosen.pattern (values m p.leaf.chosen.captures)) := by
  have valid := actual_aligned_two_nodes negative
  cases src : start negative with
  | none => rw [src] at valid; cases valid
  | some r =>
    rw [src] at valid
    change ((sequence r).bind fun s => (run s).map verify).getD false = true at valid
    cases children : sequence r with
    | none => rw [children] at valid; cases valid
    | some s =>
      rw [children] at valid
      change ((run s).map verify).getD false = true at valid
      cases built : run s with
      | none => rw [built] at valid; cases valid
      | some p =>
        rw [built] at valid
        have test := Bool.and_eq_true_iff.mp (show verify p = true from valid)
        have ids := of_decide_eq_true (Bool.and_eq_true_iff.mp test.1).1
        have same := GeneralDeclarativeWitnessNativeSnapshot360.same_exact.mp test.2
        refine ⟨r,s,p,rfl,children,built,ids.1,ids.2,?_,fun u v => ⟨same.symm ▸ model_fits u v,fun _ => rfl⟩,?_⟩
        · rw [← ids.1,← ids.2]; exact recursive_witness p
        · intro m v fit
          have proof := ordered_dictionary_sound p m v fit
          refine ⟨proof.2.2.2.2.1,?_,proof.2.2.2.2.2.2.2.2.2⟩
          have rows := fit.1.2
          rw [same] at rows
          exact rows _ (List.mem_append_right _ (by decide +kernel))

end Yulang.GeneralDeclarativeWitnessMixedForwardSound361
