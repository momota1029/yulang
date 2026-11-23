import Yulang.GeneralDeclarativeWitnessOrderedNativeRelease362

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65000
set_option maxHeartbeats 65000000
namespace Yulang.GeneralDeclarativeWitnessNativeOrder362
open GeneralDeclarativeWitnessThreeNative362 (Run run authority)
open GeneralDeclarativeWitnessOrderedNativeRelease362 (Opened read)
open GeneralDeclarativeWitnessNativeValue360 (Code)
open GeneralDeclarativeWitnessNativeInstall360 (Fits NativeViews)
open GeneralDeclarativeWitnessNativeThreeModel362 (every_fit_retains_source_window)
open GeneralDeclarativeWitnessInheritedModeFixture357 (table)
open CommonRecursiveNominalIntervals (Endpoint Bounds ContextWellFormed ResultHolds)
open GeneralDeclarativeWitnessSparseIntervals357 (Compiled)
open GeneralDeclarativeWitnessFullIntervals357 (ContextDerives compiled_full_exact)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Subtype)
open PresenceNormalForm (Atom)

/-- Read the actual authored code into explicit point arguments. True
inherited context is selected by the surrounding comparison, not by
this converter. This does not equate the native board with ordinary Ty. -/
def node : Code → Endpoint Nat
  | .leaf n => .ordinary (.var n)
  | .nullary k => .nominal k []
  | .unary k inner => .nominal k [.inl (.point (node inner))]

def low {c} (r : Run c) := node r.lower.write.code
def center {c} (r : Run c) := node r.center.write.code
def high {c} (r : Run c) := node r.upper.write.code

structure Chain {contra : Bool} (r : Run contra) where
  releases : Opened r authority
  left : Compiled r.environment table false (low r) (center r)
  right : Compiled r.environment table false (center r) (high r)

def chain {contra} (r : Run contra) : Option (Chain r) := do
  let permitted ← read r authority
  let left ← GeneralDeclarativeWitnessSparseIntervals357.compile r.environment table false (low r) (center r)
  let right ← GeneralDeclarativeWitnessSparseIntervals357.compile r.environment table false (center r) (high r)
  pure ⟨permitted,left,right⟩

def atom (a b : Nat) : Atom Nat := .tyLe (.var a) (.var b)
def leftAtom (contra : Bool) : Atom Nat := if contra then atom 61 62 else atom 60 61
def rightAtom (contra : Bool) : Atom Nat := if contra then atom 60 61 else atom 61 62

def exact {contra r} (s : @Chain contra r) : Bool :=
  decide (s.left.rows = [leftAtom contra] ∧ s.right.rows = [rightAtom contra])

theorem actual_directed_rows (contra : Bool) :
    ((run contra).bind fun r => (chain r).map exact).getD false = true := by cases contra <;> decide +kernel

theorem holds_yields_typed_context {e c lo hi} (made : Compiled e table c lo hi) (m : Assignment)
    (written : ∀ a ∈ made.rows,a.Holds CommonNominalFullCarrier.model m) :
    ContextWellFormed table c lo ∧ ContextWellFormed table c hi ∧ ContextDerives table m c lo hi :=
  (compiled_full_exact table m c lo hi).mp ⟨made.rows,made.exact,written⟩

theorem release_and_order_in_every_fit {contra} {r : Run contra} {s : Chain r}
    (ran : run contra = some r) (opened : chain r = some s) (m : Assignment) (v : NativeViews)
    (fit : Fits r.final m v) :
    (ContextWellFormed table false (low r) ∧ ContextWellFormed table false (center r) ∧
      ContextWellFormed table false (high r)) ∧
    ContextDerives table m false (low r) (center r) ∧ ContextDerives table m false (center r) (high r) ∧
    (v 201 = some (.unary (GeneralDeclarativeWitnessThreeNative362.ctor contra)
      (.leaf (m (GeneralDeclarativeWitnessThreeNative362.first contra)).1)) ∧
     v 202 = some (.unary (GeneralDeclarativeWitnessThreeNative362.ctor contra) (.leaf (m 61).1)) ∧
     v 203 = some (.unary (GeneralDeclarativeWitnessThreeNative362.ctor contra)
      (.leaf (m (GeneralDeclarativeWitnessThreeNative362.last contra)).1))) := by
  have h := actual_directed_rows contra
  rw [ran] at h
  change ((chain r).map exact).getD false = true at h
  rw [opened] at h
  have rows := of_decide_eq_true (show exact s = true from h)
  obtain ⟨_,a,b⟩ := every_fit_retains_source_window r m v fit
  have aa : (leftAtom contra).Holds CommonNominalFullCarrier.model m := by
    cases contra
    · exact a
    · exact b
  have bb : (rightAtom contra).Holds CommonNominalFullCarrier.model m := by
    cases contra
    · exact b
    · exact a
  have x := holds_yields_typed_context s.left m (by intro row present; rw [rows.1] at present; cases List.mem_singleton.mp present; exact aa)
  have y := holds_yields_typed_context s.right m (by intro row present; rw [rows.2] at present; cases List.mem_singleton.mp present; exact bb)
  exact ⟨⟨x.1,x.2.1,y.2.1⟩,x.2.2,y.2.2,
    GeneralDeclarativeWitnessOrderedNativeRelease362.source_code_in_every_fit ran s.releases m v fit⟩

end Yulang.GeneralDeclarativeWitnessNativeOrder362
