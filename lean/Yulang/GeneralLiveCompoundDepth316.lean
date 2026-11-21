import Yulang.GeneralLiveCompoundLeafEvidence316

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 24000
set_option maxHeartbeats 25000000
/-! A variant over a payload with no testable constructor cannot start an
actual-position cycle. This uses the real observability relation, not a
bound on the scheduler or termination. -/
namespace Yulang.GeneralLiveCompoundDepth316
open CommonNominalFullCarrier GeneralNominalRecursiveInspection
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedCycles232 (Cyclic Edge Path)
open GeneralNominalOriginTerms (Head arity project)
open GeneralDictionaryDefaultExpression209 (equivalent_trans)
open GeneralDictionaryInspectionHeads215 GeneralNominalFiniteHeadInversion
open GeneralNominalCommonBridge (Assignment)

theorem variant_child {m : Assignment} {root : Origin} {ty : Ty} {tag : Nat}
    (ref : ∀ a, Observes m root a → Equivalent a (variant tag ty))
    (test : Test) (index : Fin (arity test))
    (seen : Observes m (project root test index) actual) : Equivalent actual ty := by
  cases test with
  | scalar n => exact Fin.elim0 index
  | nominal name count =>
    cases seen with
    | nominal parent eq found =>
      have both := equivalent_trans ⟨(ref _ parent).2,(ref _ parent).1⟩ eq
      have tags := tag_subtype (tagged_shape (.variant tag) [ty] rfl) (tagged_nominal name _) both.1
      cases tags
  | structural shape =>
    cases seen with
    | structural parent length eq found =>
      have both := equivalent_trans ⟨(ref _ parent).2,(ref _ parent).1⟩ eq
      have tags := tag_subtype (tagged_shape (.variant tag) [ty] rfl) (tagged_shape shape _ length) both.1
      cases shape with
      | pair => cases tags
      | exactEmpty => cases tags
      | record _ => cases tags
      | variant other =>
        cases tags
        exact GeneralNominalStructuralReadback.shape_payload (.variant tag) (by trivial) _ [ty]
          length rfl found (by
            have val : index.val = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ index.isLt)
            rw [val]; rfl) ⟨both.2,both.1⟩

theorem headless_variant_no_cycle {m : Assignment} (valid : Models state m)
    (value : Equivalent (m n).1 (variant tag payload))
    (headless : ∀ t : Test, ¬ Test.Holds t payload) :
    ¬ Cyclic state (.source n) := by
  rintro ⟨⟨next,⟨parent,test,index,_,first,last⟩,tail⟩,_⟩
  have sourceValue : Observes m (.source n) (m n).1 := .source n
  have parentValue : ∀ a, Observes m parent a → Equivalent a (variant tag payload) := by
    intro a seen
    have e := (first m valid).2.2 _ _ sourceValue seen
    exact equivalent_trans ⟨e.2,e.1⟩ value
  have nextValue : ∀ a, Observes m next a → Equivalent a payload := by
    intro a seen
    obtain ⟨p,observed⟩ := (last m valid).1
    have e := (last m valid).2.2 _ _ observed seen
    exact equivalent_trans ⟨e.2,e.1⟩ (variant_child parentValue test index observed)
  cases tail with
  | nil =>
    exact headless (.structural (.variant tag))
      ⟨[payload],rfl,equivalent_trans ⟨(nextValue _ sourceValue).2,(nextValue _ sourceValue).1⟩ value⟩
  | cons edge rest =>
    obtain ⟨p,t,_,head,one,_⟩ := edge
    obtain ⟨a,seen⟩ := (one m valid).1
    obtain ⟨b,read⟩ := (head m valid).1
    have e := (one m valid).2.2 _ _ seen read
    exact headless t ((GeneralNominalOriginCongruence238.test_iff
      (equivalent_trans ⟨e.2,e.1⟩ (nextValue _ seen)) t).mp ((head m valid).2 _ read))

end Yulang.GeneralLiveCompoundDepth316
