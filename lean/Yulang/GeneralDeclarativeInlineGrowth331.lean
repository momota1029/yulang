import Yulang.GeneralDeclarativeInlineMaterial331

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeInlineGrowth331
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeGrowth327 (Extends aliases)
open GeneralDeclarativeObserverGrowth330 (spine sources_grow preserve)
open GeneralDeclarativeInlineSpine331 (Closed)
open GeneralDeclarativeInlineTrace331 (Read Args Fields)

theorem closed {s t : State} (grows : Extends s t) (known : Closed s input raw terminal) :
    Closed t input raw terminal := by
  induction known with
  | terminal c => exact .terminal c
  | field _ ih => exact .field ih
  | name known => exact .name (spine grows known)

theorem extend {s t : State} (grown : Extends s t) (known : Read s mode raw pat uses) :
    Read t mode raw pat uses :=
  Read.rec
    (motive_1 := fun mode raw code uses _ => Read t mode raw code uses)
    (motive_2 := fun mode raw codes uses _ => Args t mode raw codes uses)
    (motive_3 := fun mode raw codes uses _ => Fields t mode raw codes uses)
    (by intro _ _ _; exact .capture)
    (by intro _ _ _ _ _ _ shape link stored _ ih; exact .expose shape (aliases grown link) (grown.equations stored) ih)
    (by intro _ _ _ _ _ _ ih; exact .primitive ih)
    (by intro _ _ _ _ _ _ ih; exact .nominal ih)
    (by intro _ _ _ _ _ _ ih; exact .variant ih)
    (by intro _ _ _ _ _ _ _ _ _ one two; exact .join one two)
    (by
      intro _ _ _ _ _ _ _ _ _ _ observed distinct nonempty ordered _ terminal _ first tail
      exact .record (closed grown observed) distinct nonempty ordered first terminal tail)
    (by intro _; exact .nil)
    (by intro _ _ _ _ _ _ _ _ _ x y; exact .cons x y)
    (by intro _; exact .nil)
    (by intro _ _ _ _ _ _ _ _ _ _ x y; exact .cons x y)
    known

end Yulang.GeneralDeclarativeInlineGrowth331
