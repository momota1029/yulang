import Yulang.GeneralDeclarativeWitnessThreeNative362

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 62000
set_option maxHeartbeats 60000000
namespace Yulang.GeneralDeclarativeWitnessNativeThreeModel362
open GeneralDeclarativeWitnessThreeNative362 (Run run first last)
open GeneralDeclarativeWitnessNativeInstall360 (Fits interpreted NativeViews no_ordinary_override)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeFootprint321 (stateNames preserves_models)
open GeneralDeclarativeWitnessRecordWidthFixture359 (current)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Subtype subtype_refl)
open PresenceNormalForm (Atom)

def copies (n a b : Nat) : List (Nat × Nat) :=
  [(n,n),(n,n),(a,n),(n,a),(b,n),(n,b),(a,n),(n,b)]

def rows (contra : Bool) : List (Atom Nat) :=
  (copies (first contra) 204 205 ++ copies 61 206 207 ++ copies (last contra) 208 209).map
    fun p => .tyLe (.var p.1) (.var p.2)

def after (contra : Bool) : State :=
  ⟨⟨current.normal.ordinary ++ rows contra,current.normal.intervals⟩,current.equations⟩

def snapshot {contra} (r : Run contra) : Bool :=
  decide (r.final.ordinary.normal.ordinary = (after contra).normal.ordinary ∧
    r.final.ordinary.normal.intervals = (after contra).normal.intervals ∧
    r.final.ordinary.equations = (after contra).equations)

theorem exact_snapshot (contra : Bool) :
    ((run contra).map snapshot).getD false = true := by cases contra <;> decide +kernel

theorem model_transfer {contra} (r : Run contra) (exact : snapshot r = true) (m : Assignment) :
    Models r.final.ordinary m ↔ Models (after contra) m := by
  have same := of_decide_eq_true exact
  constructor <;> intro f
  · exact ⟨⟨fun a h => f.1.1 a (same.1.symm ▸ h),fun b h => f.1.2 b (same.2.1.symm ▸ h)⟩,
      fun eq h => f.2 eq (same.2.2.symm ▸ h)⟩
  · exact ⟨⟨fun a h => f.1.1 a (same.1 ▸ h),fun b h => f.1.2 b (same.2.1 ▸ h)⟩,
      fun eq h => f.2 eq (same.2.2 ▸ h)⟩

def model (contra pickUpper : Bool) : Assignment := fun n =>
  let old := GeneralDeclarativeWitnessRecordWidthFixture359.model pickUpper
  if n = 204 ∨ n = 205 then old (first contra)
  else if n = 206 ∨ n = 207 then old 61
  else if n = 208 ∨ n = 209 then old (last contra)
  else old n

theorem fits_after (contra pickUpper : Bool) : Models (after contra) (model contra pickUpper) := by
  let old := GeneralDeclarativeWitnessRecordWidthFixture359.model pickUpper
  have a : ∀ n ∈ stateNames current, n ≠ 204 ∧ n ≠ 205 ∧ n ≠ 206 ∧ n ≠ 207 ∧ n ≠ 208 ∧ n ≠ 209 := by
    intro n used
    have safe : (stateNames current).all
        (fun a => decide (a ≠ 204 ∧ a ≠ 205 ∧ a ≠ 206 ∧ a ≠ 207 ∧ a ≠ 208 ∧ a ≠ 209)) = true := by decide +kernel
    exact of_decide_eq_true (List.all_eq_true.mp safe _ used)
  have agrees (n : Nat) (used : n ∈ stateNames current) : old n = model contra pickUpper n := by
    obtain ⟨n4,n5,n6,n7,n8,n9⟩ := a n used
    simp [model,n4,n5,n6,n7,n8,n9,old]
  have retained := (preserves_models current agrees).mp (GeneralDeclarativeWitnessRecordWidthFixture359.model_fits pickUpper)
  refine ⟨⟨?_,retained.1.2⟩,retained.2⟩
  intro atom included
  rcases (List.mem_append.mp included : atom ∈ current.normal.ordinary ∨ atom ∈ rows contra) with came|fresh
  · exact retained.1.1 _ came
  · cases contra <;>
      simp only [rows,copies,first,last,Bool.false_eq_true,ite_false,ite_true,List.cons_append,List.nil_append,
        List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at fresh
    all_goals rcases fresh with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals exact subtype_refl _

theorem every_fit_retains_source_window {contra} (r : Run contra) (m : Assignment) (v : NativeViews)
    (fit : Fits r.final m v) : Models current m ∧ Subtype (m 60).1 (m 61).1 ∧ Subtype (m 61).1 (m 62).1 := by
  have prepared := no_ordinary_override r.prepared r.upper r.write₃ ▸ fit.1
  have source : Models current m := (GeneralDeclarativeWitnessNativePreparation360.same_model_of_prepared r.prepared m prepared).1
  exact ⟨source,source.1.1 (.tyLe (.var 60) (.var 61)) (by decide +kernel),
    source.1.1 (.tyLe (.var 61) (.var 62)) (by decide +kernel)⟩

end Yulang.GeneralDeclarativeWitnessNativeThreeModel362
