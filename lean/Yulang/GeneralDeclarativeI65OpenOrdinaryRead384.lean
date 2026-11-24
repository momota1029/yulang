import Yulang.GeneralDeclarativeI65ExactSupportReads384
import Yulang.GeneralDeclarativeGraphRows321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65

open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeBounds319 (Bound)
open GeneralDeclarativeK2Graph321 (Shape)
open GeneralDeclarativeGraphRows321 (shapeOf observed structural)

/-- Positive syntax of a local rule before its output dependencies have
been proved selected. The ordinary row is the exact one named by the
indexed need; the rule cannot derive a negative verdict from absence. -/
inductive OpenOrdinaryRead384 (direct : DirectEquation383) (s : State)
    (needs : List OutputNeed384) : Equation → Prop where
  | text : direct s row → row ∈ s.current.ordinary.equations →
      OpenOrdinaryRead384 direct s needs row
  | output {pos : Nat} {q : Request} {d : CommonRoleOutermostResolver.Dictionary} {ordinal : Nat}
      (atIndex : needs[pos]? = some (OutputNeed384.ordinary q d ordinal row)) :
      OpenOrdinaryRead384 direct s needs row

theorem close_open_ordinary_read384 {source ordinary tagged direct s needs row}
    (proofs : ExactSupportForest384 source ordinary tagged s needs)
    (read : OpenOrdinaryRead384 direct s needs row) :
    Nonempty (SourceEquationRead383 (ForgetExactRule384 source) direct ordinary s row) := by
  cases read with
  | text why live => exact ⟨.written why live⟩
  | @output pos q d ordinal there => exact (read_exact_ordinary_index384 proofs pos there).1

abbrev BoundOrigin384 := State → Nat → Nat → Prop

/-- Logical source authority for primitive interval and ordinary tyLe
edges is kept separate from their presence in normal. An output alias
cannot acquire support just because normalization moved it to tyLe. -/
inductive OpenBound384 (intervalOrigin constraintOrigin : BoundOrigin384) (s : State) :
    Nat → Nat → Prop where
  | interval : intervalOrigin s a b → (a,b) ∈ s.current.ordinary.normal.intervals →
      OpenBound384 intervalOrigin constraintOrigin s a b
  | constraint : constraintOrigin s a b →
      PresenceNormalForm.Atom.tyLe (.var a) (.var b) ∈ s.current.ordinary.normal.ordinary →
      OpenBound384 intervalOrigin constraintOrigin s a b
  | refl (a : Nat) : OpenBound384 intervalOrigin constraintOrigin s a a
  | trans : OpenBound384 intervalOrigin constraintOrigin s a b →
      OpenBound384 intervalOrigin constraintOrigin s b c →
      OpenBound384 intervalOrigin constraintOrigin s a c

theorem open_bound_is_current384 {intervalOrigin constraintOrigin s a b}
    (bound : OpenBound384 intervalOrigin constraintOrigin s a b) :
    Bound s.current.ordinary.normal a b := by
  induction bound with
  | interval _ live => exact .interval live
  | constraint _ live => exact .constraint live
  | refl => exact .refl _
  | trans _ _ l r => exact .trans l r

inductive OpenAlias384 (direct : DirectEquation383)
    (intervalOrigin constraintOrigin : BoundOrigin384) (s : State) (needs : List OutputNeed384) :
    Nat → Nat → Prop where
  | bounds : OpenBound384 intervalOrigin constraintOrigin s a b →
      OpenBound384 intervalOrigin constraintOrigin s b a →
      OpenAlias384 direct intervalOrigin constraintOrigin s needs a b
  | forward : OpenOrdinaryRead384 direct s needs ⟨a,.variable b⟩ →
      OpenAlias384 direct intervalOrigin constraintOrigin s needs a b
  | backward : OpenOrdinaryRead384 direct s needs ⟨b,.variable a⟩ →
      OpenAlias384 direct intervalOrigin constraintOrigin s needs a b
  | trans : OpenAlias384 direct intervalOrigin constraintOrigin s needs a b →
      OpenAlias384 direct intervalOrigin constraintOrigin s needs b c →
      OpenAlias384 direct intervalOrigin constraintOrigin s needs a c

theorem closed_open_read_is_current384 {source ordinary tagged direct s needs row}
    (proofs : ExactSupportForest384 source ordinary tagged s needs)
    (read : OpenOrdinaryRead384 direct s needs row) : row ∈ s.current.ordinary.equations := by
  obtain ⟨exactRead⟩ := close_open_ordinary_read384 proofs read
  cases exactRead with
  | written _ live => exact live
  | output _ _ _ _ _ live => exact live

theorem close_open_alias384 {source ordinary tagged direct intervalOrigin constraintOrigin s needs a b}
    (proofs : ExactSupportForest384 source ordinary tagged s needs)
    (path : OpenAlias384 direct intervalOrigin constraintOrigin s needs a b) :
    GeneralDeclarativeLowerKnown321.Alias s.current.ordinary a b := by
  induction path with
  | bounds lo hi => exact .bounds (open_bound_is_current384 lo) (open_bound_is_current384 hi)
  | forward step => exact .forward (closed_open_read_is_current384 proofs step)
  | backward step => exact .backward (closed_open_read_is_current384 proofs step)
  | trans _ _ l r => exact .trans l r

/-- Evidence is about this actually observed normalized constructor,
not mere entailment or a successful dictionary for another request. -/
inductive OpenObserved384 (direct : DirectEquation383)
    (intervalOrigin constraintOrigin : BoundOrigin384) (s : State)
    (needs : List OutputNeed384) : Nat → Shape → Prop where
  | shape :
      OpenAlias384 direct intervalOrigin constraintOrigin s needs atName row.left →
      OpenOrdinaryRead384 direct s needs row →
      shapeOf row.right = some shape →
      OpenObserved384 direct intervalOrigin constraintOrigin s needs atName shape

theorem close_open_observation384 {source ordinary tagged direct intervalOrigin constraintOrigin s needs atName shape}
    (proofs : ExactSupportForest384 source ordinary tagged s needs)
    (witness : OpenObserved384 direct intervalOrigin constraintOrigin s needs atName shape) :
    structural s.current.ordinary atName shape := by
  cases witness with
  | shape path read shape =>
    exact ⟨_,close_open_alias384 proofs path,_,closed_open_read_is_current384 proofs read,shape⟩

end Yulang.GeneralDeclarativeI65
