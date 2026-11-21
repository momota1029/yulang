import Yulang.GeneralDeclarativeSemanticSharing323
import Yulang.GeneralDeclarativeInequality322

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeActualPoint323
open GeneralDeclarativeHead320 (State Models environment)
open GeneralDeclarativeInequality322 (Le sound)
open GeneralDeclarativeRepeatedActual323 (eqAt)
open GeneralDeclarativeSemanticSharing323 (SameBinder)
open GeneralNominalCenteredHeadMatExpressions (Expr value)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_symm eqv_trans)
open CommonNominalFullCarrier (Equivalent subtype_trans)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarativeTermWalk322 (Occurrence)

structure Collapsed (s : State) (seen : List Occurrence) (lo hi : Nat → Expr) : Prop where
  cluster : ∀ use ∈ seen, Le s (lo use.binder) use.term ∧ Le s use.term (hi use.binder)
  point : ∀ use ∈ seen, Le s (hi use.binder) (lo use.binder)

theorem collapse {s : State} (l : Le s lower actual) (u : Le s actual upper)
    (back : Le s upper lower) (m : Assignment) (valid : Models s m) :
    eqAt m actual lower :=
  ⟨subtype_trans (sound u m valid) (sound back m valid),sound l m valid⟩

/-- Actual occurrences forced into a collapsed joint interval agree,
even when they are compound projected expressions; equality of the
endpoints of two *wide* intervals does not imply this. -/
theorem at_point {s : State} {seen : List Occurrence} (supplied : Collapsed s seen lo hi) :
    SameBinder s seen := by
  intro a pa b pb same m valid
  have one := collapse (supplied.cluster a pa).1 (supplied.cluster a pa).2 (supplied.point a pa) m valid
  have two := collapse (supplied.cluster b pb).1 (supplied.cluster b pb).2 (supplied.point b pb) m valid
  rw [same] at one
  exact eqv_trans one (eqv_symm two)

/-- Mutual bounds on each source actual expression, including compound
projections, imply sharing independently of names or interval endpoint
representation. -/
theorem one_actual {s : State} {seen : List Occurrence} {anchor : Nat → Expr}
    (names : ∀ use ∈ seen, Le s use.term (anchor use.binder) ∧ Le s (anchor use.binder) use.term) :
    SameBinder s seen := by
  intro a haveA b haveB same m valid
  have e1 : eqAt m a.term (anchor a.binder) :=
    ⟨sound (names a haveA).1 m valid,sound (names a haveA).2 m valid⟩
  have e2 : eqAt m b.term (anchor b.binder) :=
    ⟨sound (names b haveB).1 m valid,sound (names b haveB).2 m valid⟩
  rw [same] at e1
  exact eqv_trans e1 (eqv_symm e2)

end Yulang.GeneralDeclarativeActualPoint323
