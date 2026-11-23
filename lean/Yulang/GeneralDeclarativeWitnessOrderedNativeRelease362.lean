import Yulang.GeneralDeclarativeWitnessNativeThreeModel362

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65000
set_option maxHeartbeats 62000000
namespace Yulang.GeneralDeclarativeWitnessOrderedNativeRelease362
open GeneralDeclarativeWitnessThreeNative362 (Run run checked first last ctor authority address expected)
open GeneralDeclarativeWitnessNativeInstall360 (Fits NativeViews atTarget)
open GeneralDeclarativeWitnessNativeValue360 (Code Write Value)
open GeneralDeclarativeWitnessNativeRelease360 (ReleaseAuthority ExactRelease checkExactRelease checked_exact_written_value)
open GeneralNominalCommonBridge (Assignment)

structure Opened {contra : Bool} (r : Run contra) (gate : ReleaseAuthority) where
  low : ExactRelease r.final.board gate r.lower.write
  middle : ExactRelease r.final.board gate r.center.write
  high : ExactRelease r.final.board gate r.upper.write

def read {contra} (r : Run contra) (gate : ReleaseAuthority) : Option (Opened r gate) := do
  let lo ← checkExactRelease r.final.board gate r.lower.write
  let mid ← checkExactRelease r.final.board gate r.center.write
  let hi ← checkExactRelease r.final.board gate r.upper.write
  pure ⟨lo,mid,hi⟩

theorem fixture_has_three_live_releases (contra : Bool) :
    ((run contra).map fun r => (read r authority).isSome).getD false = true := by
  cases contra <;> decide +kernel

theorem exact_current_values {contra} {r : Run contra} {gate} (p : Opened r gate)
    (m : Assignment) (v : NativeViews) (fit : Fits r.final m v) :
    v r.lower.write.address.target = some (r.lower.write.code.eval m) ∧
    v r.center.write.address.target = some (r.center.write.code.eval m) ∧
    v r.upper.write.address.target = some (r.upper.write.code.eval m) :=
  ⟨checked_exact_written_value p.low m v fit,
    checked_exact_written_value p.middle m v fit,
    checked_exact_written_value p.high m v fit⟩

def withoutLow : ReleaseAuthority := ⟨[address 1,address 2]⟩
def withoutMid : ReleaseAuthority := ⟨[address 0,address 2]⟩
def withoutHigh : ReleaseAuthority := ⟨[address 0,address 1]⟩

def mutation {contra} (r : Run contra) : Bool :=
  (read r withoutLow).isNone && (read r withoutMid).isNone && (read r withoutHigh).isNone &&
  (checkExactRelease r.final.board authority
    {r.lower.write with address := {r.lower.write.address with outputOrdinal := 2}}).isNone &&
  (checkExactRelease r.final.board authority
    {r.center.write with code := r.lower.write.code}).isNone &&
  (checkExactRelease r.final.board authority
    {r.upper.write with address := {r.upper.write.address with target := 201}}).isNone

theorem independent_grants_not_recovered_by_equal_shape (contra : Bool) :
    ((run contra).map mutation).getD false = true := by cases contra <;> decide +kernel

theorem source_code_in_every_fit {contra} {r : Run contra} {gate}
    (ran : run contra = some r) (p : Opened r gate) (m : Assignment) (v : NativeViews) (fit : Fits r.final m v) :
    v 201 = some (.unary (ctor contra) (.leaf (m (first contra)).1)) ∧
    v 202 = some (.unary (ctor contra) (.leaf (m 61).1)) ∧
    v 203 = some (.unary (ctor contra) (.leaf (m (last contra)).1)) := by
  have receipts := GeneralDeclarativeWitnessThreeNative362.actual_three_authored_outputs contra
  rw [ran] at receipts
  change checked r = true at receipts
  have writes := (of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp receipts).1).1).1).2
  unfold expected at writes
  have one := (List.cons.inj writes).1
  have two := (List.cons.inj (List.cons.inj writes).2).1
  have three := (List.cons.inj (List.cons.inj (List.cons.inj writes).2).2).1
  obtain ⟨lo,mid,hi⟩ := exact_current_values p m v fit
  rw [one] at lo
  rw [two] at mid
  rw [three] at hi
  exact ⟨lo,mid,hi⟩

end Yulang.GeneralDeclarativeWitnessOrderedNativeRelease362
